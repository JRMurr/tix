# nix/scripts.nix — tixc, nixpkgs-test, nixpkgs-lib-test as Nix packages
#
# Eliminates duplicated cargo build blocks, stubs exports, systemd-run
# invocations, and nix eval calls from the shell scripts. The nixpkgs
# source path is baked in at build time (no `nix eval` at runtime).
#
# The tix binary and stubs paths are NOT build-time dependencies —
# they are string paths resolved at runtime so that building the
# scripts does not force a full Rust build.
{
  pkgs,
  nixpkgs-src,  # string: store path to nixpkgs source
}:
let
  # ==============================================================================
  # Shared bash helpers interpolated into all three scripts.
  # ==============================================================================

  sharedHelpers = ''
    # Run a command under a cgroup memory limit (Linux/systemd).
    run_with_mem_limit() {
      local mem_gb="$1"; shift
      systemd-run --user --scope -q \
        -p "MemoryMax=''${mem_gb}G" -p MemorySwapMax=0 \
        "$@"
    }

    # Resolve the tix binary. Default: cargo build from local source.
    # --release: cargo build --release.
    resolve_tix() {
      if [[ ! -f "$PWD/Cargo.toml" ]]; then
        echo "ERROR: must be run from the tix repo root (no Cargo.toml in $PWD)" >&2
        exit 2
      fi
      local cargo_args=(build --bin tix --manifest-path "$PWD/Cargo.toml")
      if [[ "''${RELEASE:-0}" -eq 1 ]]; then
        cargo_args+=(--release)
        echo "Building tix (release)..." >&2
        echo "$PWD/target/release/tix"
      else
        echo "Building tix (debug)..." >&2
        echo "$PWD/target/debug/tix"
      fi
      cargo "''${cargo_args[@]}" >&2
    }

    # Resolve stubs path: env var > repo stubs/ dir.
    resolve_stubs() {
      if [[ -n "''${TIX_BUILTIN_STUBS:-}" ]]; then
        echo "$TIX_BUILTIN_STUBS"
      elif [[ -d "$PWD/stubs" ]]; then
        echo "$PWD/stubs"
      else
        echo "WARNING: no stubs found (set TIX_BUILTIN_STUBS or run from repo root)" >&2
        echo ""
      fi
    }
  '';

  # Exclude patterns shared between nixpkgs-test and nixpkgs-lib-test.
  # Auto-generated giant package sets that blow up memory.
  nixpkgsExcludePatterns = [
    "**/tests/**"
    "**/test/**"
    "**/deprecated/**"
    "**/haskell-modules/hackage-packages.nix"
    "**/lisp-modules/imported.nix"
    "**/tex/texlive/tlpdb.nix"
    "**/tex/texlive/fixed-hashes.nix"
    "**/top-level/perl-packages.nix"
    "**/top-level/python-packages.nix"
    "**/top-level/all-packages.nix"
    "**/node-packages/node-packages.nix"
    "**/vim/plugins/generated.nix"
    "**/vim/plugins/nvim-treesitter/generated.nix"
    "**/elisp-packages/elpa-generated.nix"
    "**/elisp-packages/elpa-devel-generated.nix"
    "**/elisp-packages/nongnu-generated.nix"
    "**/elisp-packages/nongnu-devel-generated.nix"
    "**/lua-modules/generated-packages.nix"
    "**/home-assistant/component-packages.nix"
    "**/maintainers/maintainer-list.nix"
    "**/gitlab/rubyEnv/gemset.nix"
    "**/mastodon/gemset.nix"
    "**/compilers/chicken/4/default.nix"
  ];

  # Format a list of strings as a TOML array literal.
  # Inner quotes are backslash-escaped so they survive bash's echo "...".
  tomlArray = items: "[${builtins.concatStringsSep ", " (map (i: ''\"${i}\"'') items)}]";

  excludeToml = tomlArray nixpkgsExcludePatterns;
in
{
  # ============================================================================
  # tixc — type-check Nix source (stdin, file, or nixpkgs: ref)
  # ============================================================================
  tixc = pkgs.writeShellApplication {
    name = "tixc";
    runtimeInputs = with pkgs; [
      coreutils
      systemd
      time
    ];
    text = ''
      ${sharedHelpers}

      INPUT=""
      TIX_ARGS=()
      MEM_LIMIT_GB=16
      RELEASE=0
      TIMEOUT=""
      USE_TIME=0

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --release)
            RELEASE=1
            shift
            ;;
          --mem-limit)
            [[ $# -ge 2 ]] || { echo "ERROR: --mem-limit requires a value" >&2; exit 2; }
            MEM_LIMIT_GB="$2"
            shift 2
            ;;
          --timeout)
            [[ $# -ge 2 ]] || { echo "ERROR: --timeout requires a value" >&2; exit 2; }
            TIMEOUT="$2"
            shift 2
            ;;
          --time)
            USE_TIME=1
            shift
            ;;
          *)
            if [[ -z "$INPUT" && "$1" != -* ]]; then
              INPUT="$1"
            else
              TIX_ARGS+=("$1")
            fi
            shift
            ;;
        esac
      done

      TIX_CLI="$(resolve_tix)"

      if [[ -z "$INPUT" ]]; then
        # No file argument — read from stdin.
        tmpdir=$(mktemp -d)
        trap 'rm -rf "$tmpdir"' EXIT
        cat > "$tmpdir/input.nix"
        FILE="$tmpdir/input.nix"

      elif [[ "$INPUT" == nixpkgs:* ]]; then
        # nixpkgs:<subpath> — use baked nixpkgs store path.
        SUBPATH="''${INPUT#nixpkgs:}"
        FILE="${nixpkgs-src}/$SUBPATH"
        if [[ ! -f "$FILE" ]]; then
          echo "ERROR: $FILE does not exist" >&2
          exit 2
        fi

      else
        # Plain file path.
        FILE="$INPUT"
        if [[ ! -f "$FILE" ]]; then
          echo "ERROR: $FILE does not exist" >&2
          exit 2
        fi
      fi

      TIX_BUILTIN_STUBS="$(resolve_stubs)"
      export TIX_BUILTIN_STUBS

      # Build the command with optional timeout and time wrappers.
      CMD=()
      if [[ -n "$TIMEOUT" ]]; then
        CMD+=(timeout "''${TIMEOUT}s")
      fi
      if [[ "$USE_TIME" -eq 1 ]]; then
        GNU_TIME="$(command -v time)"
        CMD+=("$GNU_TIME" -v)
      fi
      CMD+=("$TIX_CLI" "$FILE" "''${TIX_ARGS[@]}")

      run_with_mem_limit "$MEM_LIMIT_GB" "''${CMD[@]}"
    '';
  };

  # ============================================================================
  # nixpkgs-test — run tix on nixpkgs .nix files (parallel via tix check)
  # ============================================================================
  nixpkgs-test = pkgs.writeShellApplication {
    name = "nixpkgs-test";
    runtimeInputs = with pkgs; [
      coreutils
      systemd
      findutils
    ];
    text = ''
      ${sharedHelpers}

      DEADLINE=30
      JOBS=""
      TIMING=0
      RELEASE=0
      VERBOSE=0
      MEM_LIMIT_GB=16
      DIRS=()

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --deadline)
            [[ $# -ge 2 ]] || { echo "ERROR: --deadline requires a value" >&2; exit 2; }
            DEADLINE="$2"
            shift 2
            ;;
          --jobs|-j)
            [[ $# -ge 2 ]] || { echo "ERROR: --jobs requires a value" >&2; exit 2; }
            JOBS="$2"
            shift 2
            ;;
          --timing)
            TIMING=1
            shift
            ;;
          --release)
            RELEASE=1
            shift
            ;;
          --verbose|-v)
            VERBOSE=1
            shift
            ;;
          --mem-limit)
            [[ $# -ge 2 ]] || { echo "ERROR: --mem-limit requires a value" >&2; exit 2; }
            MEM_LIMIT_GB="$2"
            shift 2
            ;;
          --help|-h)
            echo "Usage: nixpkgs-test [OPTIONS] [DIRS...]"
            echo ""
            echo "Check nixpkgs .nix files with tix (parallel mode)."
            echo ""
            echo "Arguments:"
            echo "  DIRS...             Subdirectories to check (default: all)"
            echo "                      Examples: lib/ pkgs/ nixos/ pkgs/by-name/"
            echo ""
            echo "Options:"
            echo "  --deadline <secs>   Per-file inference deadline (default: 30)"
            echo "  --jobs, -j <N>      Number of parallel inference threads"
            echo "  --timing            Print per-phase timing and memory usage"
            echo "  --release           Build tix in release mode"
            echo "  --verbose, -v       Print file classifications"
            echo "  --mem-limit <GB>    Memory limit for tix process (default: 16)"
            echo "  --help, -h          Show this help"
            exit 0
            ;;
          -*)
            echo "Unknown flag: $1" >&2
            echo "Run 'nixpkgs-test --help' for usage." >&2
            exit 2
            ;;
          *)
            # Strip trailing slashes for consistency.
            DIRS+=("''${1%/}")
            shift
            ;;
        esac
      done

      TIX_CLI="$(resolve_tix)"

      NIXPKGS_SRC="${nixpkgs-src}"
      if [[ ! -d "$NIXPKGS_SRC" ]]; then
        echo "ERROR: nixpkgs source not found at $NIXPKGS_SRC" >&2
        exit 2
      fi

      # Set up work dir with symlinks into the nix store (avoids copying ~450MB).
      WORK_DIR="$(mktemp -d)"
      trap 'rm -rf "$WORK_DIR"' EXIT

      if [[ ''${#DIRS[@]} -eq 0 ]]; then
        echo "Checking all of nixpkgs..."
        for entry in "$NIXPKGS_SRC"/*; do
          name="$(basename "$entry")"
          ln -s "$entry" "$WORK_DIR/$name"
        done
      else
        echo "Checking: ''${DIRS[*]}"
        for dir in "''${DIRS[@]}"; do
          top="''${dir%%/*}"
          src="$NIXPKGS_SRC/$top"
          if [[ ! -e "$src" ]]; then
            echo "WARNING: $top/ does not exist in nixpkgs, skipping" >&2
            continue
          fi
          if [[ ! -L "$WORK_DIR/$top" ]]; then
            ln -s "$src" "$WORK_DIR/$top"
          fi
        done
        # Always make lib/ available for imports.
        if [[ ! -L "$WORK_DIR/lib" ]]; then
          ln -s "$NIXPKGS_SRC/lib" "$WORK_DIR/lib"
        fi
      fi

      # Count .nix files that will be checked.
      NIX_COUNT=$(find -L "$WORK_DIR" -name '*.nix' -type f \
        ! -path '*/tests/*' \
        ! -path '*/test/*' \
        ! -path '*/deprecated/*' \
        2>/dev/null | wc -l)
      echo "Found ~''${NIX_COUNT} .nix files"
      echo "Deadline: ''${DEADLINE}s per file"

      # Generate tix.toml.
      {
        echo "# Auto-generated for nixpkgs checking."
        echo "deadline = ''${DEADLINE}"
        echo ""
        echo "[project]"
        if [[ ''${#DIRS[@]} -gt 0 ]]; then
          analyze="["
          first=1
          for dir in "''${DIRS[@]}"; do
            if [[ $first -eq 1 ]]; then first=0; else analyze+=", "; fi
            analyze+="\"''${dir}/**/*.nix\""
          done
          analyze+="]"
          echo "analyze = $analyze"
        fi
        echo "exclude = ${excludeToml}"
      } > "$WORK_DIR/tix.toml"

      echo "---"
      cat "$WORK_DIR/tix.toml"
      echo "---"

      # Build tix check args.
      CHECK_ARGS=(check --config "$WORK_DIR/tix.toml")
      if [[ -n "$JOBS" ]]; then
        CHECK_ARGS+=(-j "$JOBS")
      fi
      if [[ "$TIMING" -eq 1 ]]; then
        CHECK_ARGS+=(--timing)
      fi
      if [[ "$VERBOSE" -eq 1 ]]; then
        CHECK_ARGS+=(--verbose)
      fi

      TIX_BUILTIN_STUBS="$(resolve_stubs)"
      export TIX_BUILTIN_STUBS

      LOG_FILE="/tmp/nixpkgs-test-$(date +%Y%m%d-%H%M%S).log"
      echo "Memory limit: ''${MEM_LIMIT_GB} GB"
      echo "Running: tix ''${CHECK_ARGS[*]}"
      echo "Log file: $LOG_FILE"
      echo "---"

      # tix check exits 1 on type errors (expected), only treat crashes
      # (exit >= 2) as failures.
      set +e
      run_with_mem_limit "$MEM_LIMIT_GB" "$TIX_CLI" "''${CHECK_ARGS[@]}" 2>&1 | tee "$LOG_FILE"
      rc=''${PIPESTATUS[0]}
      set -e

      if [[ $rc -ge 2 ]]; then
        echo ""
        echo "tix check crashed (exit $rc)"
        echo "Full log: $LOG_FILE"
        exit 1
      fi

      echo "Full log: $LOG_FILE"
      exit 0
    '';
  };

  # ============================================================================
  # nixpkgs-lib-test — run tix on nixpkgs lib/ (sequential or parallel)
  # ============================================================================
  nixpkgs-lib-test = pkgs.writeShellApplication {
    name = "nixpkgs-lib-test";
    runtimeInputs = with pkgs; [
      coreutils
      systemd
      findutils
    ];
    text = ''
      ${sharedHelpers}

      DEADLINE=60
      PARALLEL=0
      JOBS=""
      TIMING=0
      RELEASE=0
      MEM_LIMIT_GB=16

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --deadline)
            [[ $# -ge 2 ]] || { echo "ERROR: --deadline requires a value" >&2; exit 2; }
            DEADLINE="$2"
            shift 2
            ;;
          --parallel)
            PARALLEL=1
            shift
            ;;
          --jobs|-j)
            [[ $# -ge 2 ]] || { echo "ERROR: --jobs requires a value" >&2; exit 2; }
            JOBS="$2"
            shift 2
            ;;
          --timing)
            TIMING=1
            shift
            ;;
          --release)
            RELEASE=1
            shift
            ;;
          --mem-limit)
            [[ $# -ge 2 ]] || { echo "ERROR: --mem-limit requires a value" >&2; exit 2; }
            MEM_LIMIT_GB="$2"
            shift 2
            ;;
          *)
            echo "Unknown flag: $1" >&2
            echo "Usage: nixpkgs-lib-test [--deadline <secs>] [--parallel] [--jobs N] [--timing] [--release] [--mem-limit <GB>]" >&2
            exit 2
            ;;
        esac
      done

      TIX_CLI="$(resolve_tix)"

      LIB_DIR="${nixpkgs-src}/lib"
      if [[ ! -d "$LIB_DIR" ]]; then
        echo "ERROR: $LIB_DIR does not exist" >&2
        exit 2
      fi

      # Stubs — exported unconditionally for both parallel and sequential modes.
      TIX_BUILTIN_STUBS="$(resolve_stubs)"
      export TIX_BUILTIN_STUBS

      # ====================================================================
      # Parallel mode: copy lib/ to work dir, generate tix.toml, tix check
      # ====================================================================

      if [[ "$PARALLEL" -eq 1 ]]; then
        WORK_DIR="$(mktemp -d)"
        trap 'rm -rf "$WORK_DIR"' EXIT

        echo "Copying $LIB_DIR → $WORK_DIR/lib ..."
        cp -a "$LIB_DIR" "$WORK_DIR/lib"
        chmod -R u+w "$WORK_DIR/lib"

        # Generate tix.toml with deadline written directly (no write-then-sed).
        cat > "$WORK_DIR/lib/tix.toml" <<TOML
      # Auto-generated for parallel nixpkgs lib/ checking.
      deadline = $DEADLINE

      [project]
      exclude = ["tests/**", "deprecated/**"]
      TOML

        echo "Generated $WORK_DIR/lib/tix.toml"
        echo "---"

        CHECK_ARGS=(check --config "$WORK_DIR/lib/tix.toml" --verbose)
        if [[ -n "$JOBS" ]]; then
          CHECK_ARGS+=(-j "$JOBS")
        fi
        if [[ "$TIMING" -eq 1 ]]; then
          CHECK_ARGS+=(--timing)
        fi

        echo "Memory limit: ''${MEM_LIMIT_GB} GB"
        echo "Running: tix ''${CHECK_ARGS[*]}"
        echo "---"

        set +e
        run_with_mem_limit "$MEM_LIMIT_GB" "$TIX_CLI" "''${CHECK_ARGS[@]}"
        rc=$?
        set -e

        if [[ $rc -ge 2 ]]; then
          echo ""
          echo "tix check crashed (exit $rc)"
          exit 1
        fi
        exit 0
      fi

      # ====================================================================
      # Sequential mode
      # ====================================================================

      mapfile -t NIX_FILES < <(
        find "$LIB_DIR" -name '*.nix' -type f \
          ! -path '*/tests/*' \
          ! -path '*/deprecated/*' \
        | sort
      )

      echo "Found ''${#NIX_FILES[@]} .nix files in $LIB_DIR"
      echo "Deadline: ''${DEADLINE}s per file"
      echo "Memory limit: ''${MEM_LIMIT_GB} GB"
      echo "---"

      pass=0
      type_error=0
      timed_out=0
      crash=0
      crash_files=()

      for f in "''${NIX_FILES[@]}"; do
        rel="''${f#"${nixpkgs-src}/"}"

        set +e
        run_with_mem_limit "$MEM_LIMIT_GB" \
          timeout "''${DEADLINE}s" "$TIX_CLI" "$f" >/dev/null 2>&1
        rc=$?
        set -e

        case $rc in
          0)
            printf "  PASS      %s\n" "$rel"
            pass=$((pass + 1))
            ;;
          1)
            printf "  TYPE_ERR  %s\n" "$rel"
            type_error=$((type_error + 1))
            ;;
          124)
            printf "  TIMEOUT   %s\n" "$rel"
            timed_out=$((timed_out + 1))
            ;;
          *)
            printf "  CRASH(%d) %s\n" "$rc" "$rel"
            crash=$((crash + 1))
            crash_files+=("$rel (exit $rc)")
            ;;
        esac
      done

      echo ""
      echo "=============================="
      echo " Summary"
      echo "=============================="
      printf "  Pass:       %d\n" "$pass"
      printf "  Type error: %d\n" "$type_error"
      printf "  Timeout:    %d\n" "$timed_out"
      printf "  Crash:      %d\n" "$crash"
      echo "------------------------------"
      printf "  Total:      %d\n" "''${#NIX_FILES[@]}"
      echo "=============================="

      if [[ $crash -gt 0 ]]; then
        echo ""
        echo "CRASHED FILES:"
        for cf in "''${crash_files[@]}"; do
          echo "  - $cf"
        done
        exit 1
      fi

      echo ""
      echo "No crashes detected."
      exit 0
    '';
  };
}
