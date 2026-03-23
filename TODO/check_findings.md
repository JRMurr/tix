# Repo-Check Findings (2026-03-23)

Snapshot: `repo-check-results/2026-03-23_02-17-14Z.json`
Total: 203 errors across 11 repos (1 timeout: home-manager)

## 1. `mkDefault`/`mkOptionDefault`/`mkOverride` stubs hide `priority` field

**~8 errors** (4 E002 missing field, 4 E001 type mismatch) across nix-darwin, nixvim

The stubs declare `mkDefault :: a -> a`, but these functions actually return
`{ _type: string, priority: int, content: a }`. Code that accesses `.priority`
on the result gets E002.

```nix
# nix-darwin:modules/nix/nixpkgs.nix:61
hasBuildPlatform = opt.buildPlatform.highestPrio < (lib.mkOptionDefault { }).priority;
#                                                                         ^^^^^^^^^ E002: missing field `priority`

# nix-darwin:modules/nix/nixpkgs.nix:70
legacyOptionsDefined = lib.optional (
  opt.system.highestPrio < (lib.mkDefault { }).priority
#                                               ^^^^^^^^^ E002: missing field `priority`
) opt.system;

# nixvim:plugins/by-name/none-ls/prettier.nix:11
# nixvim:wrappers/modules/nixpkgs.nix:13-14
# (same pattern — accessing priority on mkOverride/mkDefault result)
```

**Fix**: Update stubs for `mkDefault`, `mkOptionDefault`, `mkOverride`, `mkOrder`,
`mkBefore`, `mkAfter` etc. to return something like:

```tix
type MkOverrideResult = { _type: string, priority: int, content: a };
val mkDefault :: a -> MkOverrideResult;
val mkOptionDefault :: a -> MkOverrideResult;
val mkOverride :: int -> a -> MkOverrideResult;
```

Caveat: the NixOS module system unwraps these transparently, so most code never
sees the wrapper. The `a -> a` stub is correct for the common case. A more
nuanced fix might use a union: `a | { _type: string, priority: int, content: a }`.
Need to evaluate downstream impact before changing.

**Effort**: Low

---

## 2. Derivation + string coercion not modeled

**~5 errors** (E003) across nix-darwin, nixos-hardware

Nix coerces derivations to their `outPath` string when used with `+`. Tix's
overload resolver only handles primitive types (string, path, int, float, number).

```nix
# nixos-hardware:microsoft/surface/common/default.nix:51
patchSrc = linux-surface + "/patches/${versions.majorMinor srcVersion}";
#          ^^^^^^^^^^^^^^ Derivation (from fetchFromGitHub)
# E003: cannot apply `+` to `Derivation` and `string`

# nix-darwin:modules/services/wg-quick.nix:127
# (same pattern — derivation + string path)
```

The same issue affects attrsets with `outPath` (flake-compat pattern):

```nix
# nixos-hardware:tests/flake-compat.nix:210
# devenv:devenv-nix-backend/bootstrap/resolve-lock.nix:75
# dream2nix:dev-flake/flake-compat.nix:234
# E003: cannot apply `+` to `{ lastModified: int, lastModifiedDate: string, outPath: ... }` and `string`
```

**Fix**: In `try_resolve_overload` (infer.rs), when the operator is `Add` and
the LHS resolves to an AttrSet containing an `outPath: string` field, treat
it as string concatenation (return `string`). This matches Nix's coercion
semantics for `+` (but not for string interpolation, which uses `__toString`
or `outPath` — that's separate).

**Effort**: Medium

---

## 3. Cross-file optional parameter typed as default only

**~13 errors** (E001) all in nixvim telescope extensions

When a function has `settingsExample ? null` and is exported cross-file,
the parameter type is fixed to `null` (the default). Callers passing attrsets
get a type mismatch.

```nix
# nixvim:plugins/by-name/telescope/extensions/_mk-extension.nix:7
{
  settingsExample ? null,   # <-- parameter type becomes `null`
  ...
}:
...

# nixvim:plugins/by-name/telescope/extensions/advanced-git-search.nix:4
mkExtension {
  settingsExample = {       # <-- E001: expected `null`, got `{ ... }`
    diff_plugin = "diffview";
    git_flags = [ "-c" "delta.side-by-side=false" ];
  };
}

# Same pattern in: file-browser.nix, frecency.nix, live-greps-args.nix,
# manix.nix, media-files.nix, project.nix, ui-select.nix, undo.nix,
# zf-native.nix, zoxide.nix
```

**Root cause**: In cross-file inference, the function's exported signature uses
the parameter's inferred type from its own file only. Since `settingsExample`
is only used as `example = settingsExample` (passed through), and the default
is `null`, the type stays `null`. Call-site arguments from other files don't
widen it.

Within a single file this works — `constrain(default_ty, name_ty)` and
`constrain(arg_ty, name_ty)` both add lower bounds, producing a union.
Cross-file, the function type is frozen before callers are analyzed.

**Fix**: Options:
- Widen optional parameter types to `Top` in exported signatures (too loose)
- Use `null | Top` for null-defaulted optional params (still too loose)
- Accept this as a known limitation of modular type checking

Also appears in nixvim `wrappers/hm.nix:20` and `wrappers/nixos.nix:20`
(`expected null, got [string]`) — same pattern.

**Effort**: Hard (architectural)

---

## 4. `number` result from `*` doesn't flow to `int`

**1 error** (E001) in nix-colors

When `*` has one polymorphic operand, the result is typed `Number` (the
synthetic supertype of int/float). If this result flows into a function
expecting `int`, it fails because `Number </: Int`.

```nix
# nix-colors:lib/contrib/default.nix:79  (via textmate-theme.nix:16)
indentation = lib.fixedWidthString (indentLevel * (builtins.stringLength indentPattern)) indentPattern "";
#                                   ^^^^^^^^^^^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
#                                   type var      int (from stringLength)
#                                   result: number
#                                   fixedWidthString expects: int
# E001: type mismatch: expected `int`, got `number`
```

**Root cause**: `*` uses `immediate_bound: Some(PrimitiveTy::Number)` which
constrains both operands and result to `Number`. Even when one operand is
concretely `int`, the result stays `Number` because the other operand is a
type variable bounded by `Number` (could be float).

When `indentLevel` is later constrained to `int` (from call-site), the `*`
result has already been pinned to `Number` and won't refine.

**Fix**: In deferred overload resolution, when both operands resolve to `Int`,
the result should be `Int` not `Number`. The `resolve_numeric_result` function
already handles this correctly — the issue is that full resolution doesn't
re-run after both operands become concrete. Could add a re-check pass or
track arithmetic results as variables until both operands are known.

**Effort**: Medium

---

## 5. `||` narrowing misapplies negation in closures

**2 errors** (E001) in nixpkgs-lib gvariant.nix

```nix
# nixpkgs-lib:gvariant.nix:141 and :149
# E001: type mismatch: expected `bool | float`, got `int`
```

When `builtins.isInt v` narrows `v` to `int` in the then-branch, and a lambda
inside that branch uses `||` with comparisons involving `v`, the narrowing
logic misapplies negation types. The `||` analysis doesn't properly isolate
which variable each predicate's narrowing applies to when closures capture
outer narrowed bindings.

**Fix**: Investigate `||` narrowing scope isolation in `infer_expr.rs`
(`infer_with_narrowing` / `compute_narrow_override`). The narrowing predicates
from the `||` sub-expressions need to be scoped to their own variables, not
leak into the closure-captured variable's narrowing context.

**Effort**: Medium-High

---

## 6. `Path + string` fails in recursive functions

**2 errors** (E003) in nixpkgs-lib fileset/internal.nix

```nix
# nixpkgs-lib:fileset/internal.nix:356
normalisedSubtrees = mapAttrs (name: _normaliseTreeFilter (path + "/${name}")) entries;
# E003: cannot apply `+` to `Path` and `string`

# nixpkgs-lib:fileset/internal.nix:989
mapAttrs (name: lhsValue: _differenceTree (path + "/${name}") lhsValue (rhs.${name} or null)) (
# E003: cannot apply `+` to `Path` and `string`
```

Simple `path + "string"` works in tix. The issue here is that `path` is a
function parameter in a recursive function (`_normaliseTreeFilter` calls itself).
The parameter's type isn't pinned to `Path` by the time the deferred overload
resolution fixed-point loop stalls.

Confirmed: `path + "/foo"` works in isolation. The overload resolver's
`find_concrete_through_inter` likely returns `None` for the parameter variable
because its concrete type hasn't propagated yet.

**Fix**: Investigate whether the overload resolution fixed-point loop gives up
too early, or whether the `Path` lower bound isn't installed on the parameter
variable before the `+` overload tries to resolve.

**Effort**: Medium

---

## 7. Correct errors (not tix bugs)

These are legitimate type errors or known limitations, not worth fixing:

- **E015 interpolation errors (4)**: `null`, `null | string`, `int` in
  interpolation — all correct, Nix doesn't auto-coerce these
- **`string + string` with unresolved imports (1)**: `kernelConfig` imported
  from a file not in the analysis set, so its type is unknown
- **`{ ... } + int` (1)**: nix-darwin `checks.nix:69` — likely a real issue
  in the code or an unresolved import
- **NixOS module system patterns**: assertions returning `[{ assertion, message }]`
  where `string` is expected (the module system processes these specially)
- **Missing fields from unresolved imports**: `E002` errors where the attrset
  type comes from an import that wasn't analyzed or has an incomplete type

---

## Summary table

| # | Issue | Errors | Effort | Priority |
|---|-------|--------|--------|----------|
| 1 | `mkDefault` etc. stubs hide `priority` | ~8 | Low | High |
| 2 | Derivation/outPath + string coercion | ~5 | Medium | High |
| 3 | Cross-file optional param typed as default | ~13 | Hard | Low |
| 4 | `number` result from `*` won't refine to `int` | ~1 | Medium | Medium |
| 5 | `\|\|` narrowing scope leak in closures | ~2 | Medium-High | Medium |
| 6 | `Path + string` in recursive functions | ~2 | Medium | Medium |
| 7 | Correct errors (not bugs) | ~30+ | N/A | N/A |
