#!/usr/bin/env python3
"""
Generate stubs/lib.tix from noogle data-json.

Calls `nix build 'github:nix-community/noogle#data-json'` to obtain structured
data about nixpkgs lib functions, then translates their type signatures and
descriptions into .tix declaration syntax.

Usage:
    python3 scripts/gen_lib_stubs.py > stubs/lib.tix
"""

import json
import re
import subprocess
import sys
import textwrap
from collections import defaultdict
from dataclasses import dataclass, field


# =============================================================================
# Configuration
# =============================================================================

# Modules to skip — purely data, not useful for typing.
SKIP_MODULES = {
    "maintainers",
    "licenses",
    "licensesSpdx",
    "teams",
    "platforms",
    "sourceTypes",
    "kernel",
    "systems",
    # types is manually maintained below (values + nested submodules, not
    # functions with translatable noogle signatures).
    "types",
}

# Maximum line width for doc comments before wrapping.
DOC_WIDTH = 78

# Manual type overrides for functions that noogle doesn't have signatures for.
# These are mostly builtins that noogle can't extract types from.
# Key: (module_or_None, func_name), Value: .tix type signature.
MANUAL_OVERRIDES: dict[tuple[str | None, str], str] = {
    # lists builtins
    ("lists", "map"): "(a -> b) -> [a] -> [b]",
    ("lists", "filter"): "(a -> bool) -> [a] -> [a]",
    ("lists", "head"): "[a] -> a",
    ("lists", "tail"): "[a] -> [a]",
    ("lists", "length"): "[a] -> int",
    ("lists", "elem"): "a -> [a] -> bool",
    # flatten actually handles any nesting depth, but [[a]] -> [a] is the best
    # approximation in a non-recursive type system (covers the common 1-level case).
    ("lists", "flatten"): "[[a]] -> [a]",
    ("lists", "groupBy"): "(a -> string) -> [a] -> { _: [a], ... }",
    ("lists", "concatLists"): "[[a]] -> [a]",
    ("lists", "naturalSort"): "[string] -> [string]",
    ("lists", "compareLists"): "(a -> a -> int) -> [a] -> [a] -> int",
    ("lists", "subtractLists"): "[a] -> [a] -> [a]",
    ("lists", "intersectLists"): "[a] -> [a] -> [a]",
    ("lists", "mutuallyExclusive"): "[a] -> [a] -> bool",
    ("lists", "crossLists"): "(a -> b -> c) -> [a] -> [b] -> [c]",
    # findFirst's default value can differ from list element type — the return
    # is a union of the element type and the default type.
    ("lists", "findFirst"): "(a -> bool) -> b -> [a] -> (a | b)",
    # attrsets builtins
    ("attrsets", "attrNames"): "{ ... } -> [string]",
    ("attrsets", "hasAttr"): "string -> { ... } -> bool",
    ("attrsets", "getAttr"): "string -> { _: a, ... } -> a",
    ("attrsets", "listToAttrs"): "[{ name: string, value: a }] -> { _: a, ... }",
    ("attrsets", "isAttrs"): "a -> bool",
    # strings builtins
    ("strings", "replaceStrings"): "[string] -> [string] -> string -> string",
    # Top-level re-exports of the above
    (None, "map"): "(a -> b) -> [a] -> [b]",
    (None, "filter"): "(a -> bool) -> [a] -> [a]",
    (None, "head"): "[a] -> a",
    (None, "tail"): "[a] -> [a]",
    (None, "length"): "[a] -> int",
    (None, "elem"): "a -> [a] -> bool",
    (None, "flatten"): "[[a]] -> [a]",
    (None, "groupBy"): "(a -> string) -> [a] -> { _: [a], ... }",
    (None, "concatLists"): "[[a]] -> [a]",
    (None, "attrNames"): "{ ... } -> [string]",
    (None, "hasAttr"): "string -> { ... } -> bool",
    (None, "getAttr"): "string -> { _: a, ... } -> a",
    (None, "listToAttrs"): "[{ name: string, value: a }] -> { _: a, ... }",
    (None, "isAttrs"): "a -> bool",
    (None, "findFirst"): "(a -> bool) -> b -> [a] -> (a | b)",
    (None, "replaceStrings"): "[string] -> [string] -> string -> string",
    (None, "naturalSort"): "[string] -> [string]",
    (None, "subtractLists"): "[a] -> [a] -> [a]",
    (None, "intersectLists"): "[a] -> [a] -> [a]",
    # ---- lib.options (NixOS module system) ----
    ("options", "mkOption"): "{ ... } -> { ... }",
    ("options", "mkEnableOption"): "string -> { ... }",
    ("options", "mkPackageOption"): "{ ... } -> (string | [string]) -> { ... } -> { ... }",
    ("options", "mkSinkUndeclaredOptions"): "{ ... } -> { ... }",
    ("options", "literalExpression"): "string -> { ... }",
    ("options", "literalMD"): "string -> { ... }",
    ("options", "showOption"): "[string] -> string",
    ("options", "showDefs"): "[{ file: string, value: a }] -> string",
    ("options", "showFiles"): "[string] -> string",
    ("options", "mergeOneOption"): "[string] -> [{ file: string, value: a }] -> a",
    ("options", "mergeEqualOption"): "[string] -> [{ file: string, value: a }] -> a",
    ("options", "getValues"): "[{ value: a }] -> [a]",
    ("options", "getFiles"): "[{ file: a }] -> [a]",
    # ---- lib.modules (NixOS module system) ----
    ("modules", "mkIf"): "bool -> a -> a",
    ("modules", "mkMerge"): "[a] -> a",
    ("modules", "mkOverride"): "int -> a -> a",
    ("modules", "mkDefault"): "a -> a",
    ("modules", "mkForce"): "a -> a",
    ("modules", "mkOptionDefault"): "a -> a",
    ("modules", "mkImageMediaOverride"): "a -> a",
    ("modules", "mkVMOverride"): "a -> a",
    ("modules", "mkOrder"): "int -> a -> a",
    ("modules", "mkBefore"): "a -> a",
    ("modules", "mkAfter"): "a -> a",
    ("modules", "mkRenamedOptionModule"): "[string] -> [string] -> { ... }",
    ("modules", "mkRemovedOptionModule"): "[string] -> string -> { ... }",
    ("modules", "mkAliasOptionModule"): "[string] -> [string] -> { ... }",
    ("modules", "mkChangedOptionModule"): "[string] -> [string] -> (a -> b) -> { ... }",
    ("modules", "mkMergedOptionModule"): "[[string]] -> [string] -> ([a] -> b) -> { ... }",
    ("modules", "evalModules"): "{ ... } -> { ... }",
    ("modules", "mkDerivedConfig"): "{ ... } -> (a -> b) -> b",
    ("modules", "importApply"): "path -> a -> { ... }",
    # ---- top-level re-exports of NixOS module system functions ----
    (None, "mkIf"): "bool -> a -> a",
    (None, "mkMerge"): "[a] -> a",
    (None, "mkOverride"): "int -> a -> a",
    (None, "mkDefault"): "a -> a",
    (None, "mkForce"): "a -> a",
    (None, "mkOptionDefault"): "a -> a",
    (None, "mkOrder"): "int -> a -> a",
    (None, "mkBefore"): "a -> a",
    (None, "mkAfter"): "a -> a",
    (None, "mkOption"): "{ ... } -> { ... }",
    (None, "mkEnableOption"): "string -> { ... }",
    (None, "mkPackageOption"): "{ ... } -> (string | [string]) -> { ... } -> { ... }",
    (None, "mkSinkUndeclaredOptions"): "{ ... } -> { ... }",
    (None, "literalExpression"): "string -> { ... }",
    (None, "literalMD"): "string -> { ... }",
    (None, "evalModules"): "{ ... } -> { ... }",
    (None, "mkRenamedOptionModule"): "[string] -> [string] -> { ... }",
    (None, "mkRemovedOptionModule"): "[string] -> string -> { ... }",
    (None, "mkAliasOptionModule"): "[string] -> [string] -> { ... }",
    (None, "showOption"): "[string] -> string",
}

# Manual declarations for the lib.types module. Noogle entries for types are
# opaque values (not functions) and include nested submodules, so they can't
# go through the normal translation pipeline.
# Each entry is (val_name, type_signature, doc_comment_or_None).
MANUAL_TYPES_ENTRIES: list[tuple[str, str, str | None]] = [
    # Primitive types
    ("bool", "OptionType", "A boolean type (true or false)."),
    ("int", "OptionType", "A signed integer type."),
    ("float", "OptionType", "A floating-point number type."),
    ("number", "OptionType", "An integer or floating-point number type."),
    ("str", "OptionType", "A string type (single definition only; use lines for merging)."),
    ("singleLineStr", "OptionType", "A string that must not contain newline characters."),
    ("lines", "OptionType", "A string type where multiple definitions are merged with newlines."),
    ("commas", "OptionType", "A string type where multiple definitions are merged with commas."),
    ("envVar", "OptionType", "A string type where multiple definitions are merged with colons."),
    ("path", "OptionType", "A filesystem path type."),
    ("pathInStore", "OptionType", "A path that must be in the Nix store."),
    ("package", "OptionType", "A Nix derivation (package) type."),
    ("pkgs", "OptionType", "A nixpkgs package set type."),
    ("attrs", "OptionType", "A free-form attribute set with no type checking on values."),
    ("anything", "OptionType", "Accepts any value; attribute sets are merged recursively."),
    ("raw", "OptionType", "Accepts any value with no merging (exactly one definition)."),
    ("optionType", "OptionType", "A type whose values are themselves option types."),
    # Parameterized / composed types
    ("enum", "[a] -> OptionType", "An enumeration type accepting one value from a given list."),
    ("nullOr", "OptionType -> OptionType", "Accepts null or a value of the given type."),
    ("listOf", "OptionType -> OptionType", "A list where all elements have the given type."),
    ("nonEmptyListOf", "OptionType -> OptionType", "Like listOf but the merged list must contain at least one element."),
    ("attrsOf", "OptionType -> OptionType", "An attribute set where all values have the given type."),
    ("lazyAttrsOf", "OptionType -> OptionType", "Like attrsOf but lazy in its values."),
    ("either", "OptionType -> OptionType -> OptionType", "A value that is either of type t1 or t2."),
    ("oneOf", "[OptionType] -> OptionType", "A value that matches one of the given types."),
    ("coercedTo", "OptionType -> (a -> b) -> OptionType -> OptionType", "Accepts fromType (coerced via function) or toType directly."),
    ("functionTo", "OptionType -> OptionType", "A function that returns a value of the given type."),
    ("submodule", "({ ... } | ({ ... } -> { ... })) -> OptionType", "Defines a set of sub-options handled like a separate module."),
    ("submoduleWith", "{ ... } -> OptionType", "Like submodule but with more options (modules, specialArgs, etc.)."),
    ("deferredModule", "OptionType", "A module that is not yet evaluated (deferred for later composition)."),
    ("deferredModuleWith", "{ ... } -> OptionType", "Like deferredModule but accepts statically known modules."),
    ("attrTag", "{ ... } -> OptionType", "A tagged union type where each attribute represents a variant."),
    ("uniq", "OptionType -> OptionType", "Wraps a type to prevent merging (error on multiple definitions)."),
    ("unique", "{ ... } -> OptionType -> OptionType", "Like uniq but allows multiple definitions if they are all equal."),
    ("addCheck", "OptionType -> (a -> bool) -> OptionType", "Extends a type with an additional validation check function."),
    ("mkOptionType", "{ ... } -> OptionType", "Creates a custom option type."),
    ("strMatching", "string -> OptionType", "A string that must match the given regular expression."),
    ("separatedString", "string -> OptionType", "A string type where definitions are merged with the given separator."),
    ("passwdEntry", "OptionType -> OptionType", "Wraps a type to ensure values are safe for /etc/passwd format."),
    ("port", "OptionType", "A TCP/UDP port number (0 to 65535)."),
]

# Submodules nested inside lib.types.
# Key: submodule name, Value: list of (val_name, type_signature, doc).
MANUAL_TYPES_SUBMODULES: dict[str, list[tuple[str, str, str | None]]] = {
    "ints": [
        ("positive", "OptionType", "A positive integer (> 0)."),
        ("unsigned", "OptionType", "An unsigned integer (>= 0)."),
        ("between", "int -> int -> OptionType", "An integer in a specified inclusive range."),
        ("s8", "OptionType", "A signed 8-bit integer (-128 to 127)."),
        ("s16", "OptionType", "A signed 16-bit integer (-32768 to 32767)."),
        ("s32", "OptionType", "A signed 32-bit integer."),
        ("u8", "OptionType", "An unsigned 8-bit integer (0 to 255)."),
        ("u16", "OptionType", "An unsigned 16-bit integer (0 to 65535)."),
        ("u32", "OptionType", "An unsigned 32-bit integer."),
    ],
}


# =============================================================================
# Data loading
# =============================================================================


def load_noogle_data() -> list[dict]:
    """Build noogle data-json via nix and load the JSON."""
    result = subprocess.run(
        [
            "nix",
            "build",
            "github:nix-community/noogle#data-json",
            "--no-link",
            "--print-out-paths",
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    store_path = result.stdout.strip()
    with open(store_path) as f:
        return json.load(f)


# =============================================================================
# Signature translation (noogle → .tix)
# =============================================================================

# Noogle uses Haskell-ish type notation. We need to translate to .tix syntax.
# Key differences:
#   - Uppercase primitive names: String → string, Bool → bool, etc.
#   - AttrSet → { ... }
#   - Record fields use `::` and `;` in noogle, `:` and `,` in .tix
#   - ListOf X → [X] (rare but possible)
#   - ComparableVal → a (not expressible, use type var)
#   - Map String Bool → { _: bool, ... } (approximation)

# Primitive name mapping. Noogle uses Haskell-style capitalized names;
# .tix uses lowercase.
PRIMITIVE_MAP = {
    "String": "string",
    "Bool": "bool",
    "Boolean": "bool",
    "Int": "int",
    "Float": "float",
    "Path": "path",
    "Null": "null",
    "Number": "int | float",
}

# Types that map to type variables (not expressible in the type system).
TYVAR_REPLACEMENTS = {
    "ComparableVal": "a",
    "Value": "a",
    "SourceLike": "a",
    "sourceLike": "a",
    "Source": "a",
}

# Lowercase type names that should be replaced with { ... } (open attrset).
ATTRSET_ALIASES = {"attrs", "Attrs", "AttrSets"}

# Types that stay as alias references.
KEEP_AS_ALIAS = {"Derivation", "FileSet", "Any"}

# Tokens that indicate a signature is too complex to auto-translate.
COMPLEX_MARKERS = [
    "Pseudo code",
    "# ",  # inline comments in the sig
    "let\n",
    "let ",
    "where ",
    "<",  # angle brackets (e.g. `<functions>`, `<return type>`)
]


@dataclass
class TranslationResult:
    """Result of translating a noogle signature to .tix syntax."""

    tix_sig: str | None  # None if translation failed
    needs_review: bool = False
    reason: str = ""


def is_complex_signature(sig: str) -> bool:
    """Check if the signature contains pseudo-code or other untranslatable notation."""
    for marker in COMPLEX_MARKERS:
        if marker in sig:
            return True
    # Multi-line sigs with multiple `::` definitions (inline type aliases)
    lines = sig.strip().split("\n")
    double_colon_lines = [l for l in lines if "::" in l]
    if len(double_colon_lines) > 1:
        return True
    return False


def extract_main_signature(sig: str) -> str | None:
    """Extract the main 'name :: type' line from a possibly multi-line signature.

    Returns just the type part (after ::), or None if we can't parse it.
    """
    sig = sig.strip()

    # Single-line signature: "name :: type" or just "type"
    if "\n" not in sig:
        if "::" in sig:
            _, _, type_part = sig.partition("::")
            return type_part.strip()
        elif ":" in sig and not sig.startswith("{"):
            # Some use single colon: "functionArgs : (a -> b) -> Map String Bool"
            _, _, type_part = sig.partition(":")
            return type_part.strip()
        elif "=" in sig and "->" in sig:
            # Some use "name = type" (e.g. "escapeC = [string] -> string -> string")
            _, _, type_part = sig.partition("=")
            return type_part.strip()
        else:
            return sig.strip()

    # Multi-line: take the first `name :: ...` and concatenate continuation lines
    # until we hit another `::` definition or end of string.
    lines = sig.strip().split("\n")
    first_line = lines[0].strip()
    if "::" in first_line:
        _, _, type_part = first_line.partition("::")
        result_lines = [type_part.strip()]
        for line in lines[1:]:
            stripped = line.strip()
            # Stop if we hit another type definition
            if "::" in stripped and not stripped.startswith("{"):
                break
            result_lines.append(stripped)
        return " ".join(result_lines)
    return None


def translate_type_expr(expr: str) -> str:
    """Translate a single type expression from noogle notation to .tix syntax.

    This operates on the type part (after stripping the `name ::` prefix).
    """
    expr = expr.strip()
    if not expr:
        return expr

    # Replace primitive type names (only whole words).
    for noogle_name, tix_name in PRIMITIVE_MAP.items():
        expr = re.sub(rf"\b{noogle_name}\b", tix_name, expr)

    # Replace ComparableVal etc. with type vars.
    for noogle_name, tix_name in TYVAR_REPLACEMENTS.items():
        expr = re.sub(rf"\b{noogle_name}\b", tix_name, expr)

    # AttrSet / Attrs / attrs → { ... }
    expr = re.sub(r"\bAttrSet\b", "{ ... }", expr)
    for alias in ATTRSET_ALIASES:
        expr = re.sub(rf"\b{alias}\b", "{ ... }", expr)

    # Lowercase `any` → `a` (type variable, since tix has no top type yet)
    expr = re.sub(r"\bany\b", "a", expr)

    # `package` → `Derivation` (common noogle-ism)
    expr = re.sub(r"\bpackage\b", "Derivation", expr)

    # "List string" or "List a" → [string] or [a]  (Haskell-style application)
    # But NOT "List" alone (which is just AttrSet-like).
    # Also handle "ListOf X"
    expr = re.sub(
        r"\bListOf\s+(\w+)\b", lambda m: f"[{m.group(1)}]", expr
    )
    expr = re.sub(
        r"\bList\s+(\w+)\b", lambda m: f"[{m.group(1)}]", expr
    )
    # Bare "List" → [a]
    expr = re.sub(r"\bList\b", "[a]", expr)

    # "Map String Bool" → { _: bool, ... }  (approximation)
    expr = re.sub(
        r"\bMap\s+string\s+(\w+)\b",
        lambda m: f"{{ _: {m.group(1)}, ... }}",
        expr,
    )
    # Bare "Map" → { ... }
    expr = re.sub(r"\bMap\b", "{ ... }", expr)

    # Translate record syntax: { foo :: Type; bar :: Type; }
    # to .tix syntax: { foo: Type, bar: Type }
    # This is a simplified regex — handles the common cases.
    expr = translate_record_fields(expr)

    # Clean up double spaces
    expr = re.sub(r"  +", " ", expr)

    return expr.strip()


def translate_record_fields(expr: str) -> str:
    """Translate noogle record field syntax to .tix syntax.

    Noogle: { foo :: Type; bar :: Type; }
    .tix:   { foo: Type, bar: Type, ... }
    """
    # Replace `::` inside braces with `:` and `;` with `,`
    # We need to be careful to only do this inside `{ ... }` blocks.
    result = []
    depth = 0
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch == "{":
            depth += 1
            result.append(ch)
            i += 1
        elif ch == "}":
            depth -= 1
            result.append(ch)
            i += 1
        elif depth > 0 and ch == ":" and i + 1 < len(expr) and expr[i + 1] == ":":
            # Replace :: with :
            result.append(":")
            i += 2
        elif depth > 0 and ch == ";":
            result.append(",")
            i += 1
        else:
            result.append(ch)
            i += 1
    return "".join(result)


def fixup_tix_record(expr: str) -> str:
    """Post-process translated records to ensure .tix syntax compliance.

    - Remove trailing commas before `}`
    - Ensure open records have `...` before closing brace
    - Handle `?` optional field markers → remove them (tix doesn't support optional fields in sigs)
    """
    # Remove `?` from field names (e.g., `newScope?` → `newScope`)
    expr = re.sub(r"(\w)\?(\s*:)", r"\1\2", expr)

    # Remove default values after `?` in record fields (e.g., `bool ? false` → `bool`)
    expr = re.sub(r"(\w+)\s*\?\s*\w+", r"\1", expr)

    # Clean up trailing commas: ", }" → " }"
    expr = re.sub(r",\s*}", " }", expr)

    # Clean up empty trailing comma after `...`: "..., }" → "... }"
    expr = re.sub(r"\.\.\.\s*,\s*}", "... }", expr)

    # Handle `{ ... : type }` (noogle's dynamic field syntax) → `{ _: type, ... }`
    expr = re.sub(r"\{\s*\.\.\.\s*:\s*(\w+)\s*}", r"{ _: \1, ... }", expr)

    return expr


def translate_signature(sig: str) -> TranslationResult:
    """Translate a noogle type signature to .tix syntax.

    Returns a TranslationResult with the translated signature or a reason for failure.
    """
    if not sig or not sig.strip():
        return TranslationResult(None, True, "empty signature")

    if is_complex_signature(sig):
        return TranslationResult(None, True, "complex/multi-definition signature")

    type_expr = extract_main_signature(sig)
    if type_expr is None:
        return TranslationResult(None, True, "could not extract type from signature")

    translated = translate_type_expr(type_expr)
    translated = fixup_tix_record(translated)

    # Sanity check: the result should be parseable-looking.
    if "::" in translated:
        return TranslationResult(None, True, "residual :: in translated type")

    if not check_balanced(translated):
        return TranslationResult(None, True, "unbalanced braces/brackets")

    # Reject signatures with stray characters that .tix can't parse.
    if "$" in translated:
        return TranslationResult(None, True, "contains $ interpolation")
    # Trailing prose (e.g. "..., for comparable b")
    if re.search(r",\s+for\s+", translated):
        return TranslationResult(None, True, "contains trailing prose")
    # Stray `-` that isn't part of `->` (e.g. "int - b")
    without_arrows = translated.replace("->", "ARROW")
    if re.search(r"\w\s+-\s+\w", without_arrows):
        return TranslationResult(None, True, "contains stray minus operator")
    # Reject unresolved type-like tokens: `scope`, `option`, `package`, `Source`
    # that aren't real .tix types and would confuse the parser.
    # (These are noogle-isms that don't map to our type system.)
    if re.search(r"\bscope\b", translated):
        return TranslationResult(None, True, "contains unresolved type 'scope'")
    if re.search(r"\boption\b", translated):
        return TranslationResult(None, True, "contains unresolved type 'option'")

    # Replace `gvariant` with `a` (not a real type in tix)
    translated = re.sub(r"\bgvariant\b", "a", translated)

    # Ensure `|` in unions has spaces (e.g. `string|[string]` → `string | [string]`)
    translated = re.sub(r"(\S)\|(\S)", r"\1 | \2", translated)
    translated = re.sub(r"(\S)\|", r"\1 |", translated)
    translated = re.sub(r"\|(\S)", r"| \1", translated)

    # Final validation: reject if we have multi-char lowercase identifiers
    # that aren't known primitives or keywords. In .tix, only single-letter
    # lowercase names are valid type variables. Multi-char lowercase names
    # (like `sourceLike`, `gvariant`, `scope`) indicate untranslated noogle
    # types that would cause parse errors.
    VALID_LOWERCASE = {"string", "bool", "int", "float", "path", "null"}
    words = re.findall(r"\b([a-z][a-zA-Z0-9]+)\b", translated)
    for word in words:
        if word not in VALID_LOWERCASE:
            return TranslationResult(None, True, f"contains unknown type '{word}'")

    return TranslationResult(translated)


def check_balanced(s: str) -> bool:
    """Check that braces, brackets, and parens are balanced."""
    stack = []
    pairs = {")": "(", "]": "[", "}": "{"}
    for ch in s:
        if ch in "([{":
            stack.append(ch)
        elif ch in ")]}":
            if not stack or stack[-1] != pairs[ch]:
                return False
            stack.pop()
    return len(stack) == 0


# =============================================================================
# Doc comment extraction
# =============================================================================


def extract_description(content: dict | None) -> str | None:
    """Extract a short description from noogle content.

    Takes the first paragraph (before # Inputs, # Type, # Examples, etc.).
    """
    if content is None:
        return None
    text = content.get("content")
    if not text:
        return None

    text = text.strip()

    # Split at section headers.
    for header in ["# Inputs", "# Type", "# Examples", "# Notes", ":::{.example}", ":::{.warning}"]:
        idx = text.find(header)
        if idx > 0:
            text = text[:idx]

    text = text.strip()
    if not text:
        return None

    # Take just the first paragraph (up to double newline).
    paragraphs = re.split(r"\n\s*\n", text)
    first_para = paragraphs[0].strip()

    # Clean up markdown formatting.
    first_para = re.sub(r"`([^`]+)`", r"\1", first_para)  # inline code
    first_para = re.sub(r"\*([^*]+)\*", r"\1", first_para)  # emphasis
    first_para = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", first_para)  # links

    # Collapse to single line.
    first_para = " ".join(first_para.split())

    # Truncate very long descriptions.
    if len(first_para) > 200:
        first_para = first_para[:197] + "..."

    return first_para if first_para else None


# =============================================================================
# Entry grouping and deduplication
# =============================================================================


@dataclass
class FuncEntry:
    """A single lib function entry."""

    name: str
    module: str | None  # None for top-level
    path: list[str]
    signature: str | None  # raw noogle signature
    description: str | None
    tix_sig: str | None = None  # translated .tix signature
    needs_review: bool = False
    review_reason: str = ""


def process_entries(data: list[dict]) -> tuple[dict[str, list[FuncEntry]], list[FuncEntry]]:
    """Process noogle data into module-grouped entries and top-level re-exports.

    Returns:
        (modules, top_level) where modules is {module_name: [entries]}
        and top_level is [entries] for lib.X re-exports.
    """
    lib_entries = [e for e in data if e["meta"]["path"][0] == "lib"]

    # Separate into module entries (lib.module.func) and top-level (lib.func).
    module_entries: dict[str, list[FuncEntry]] = defaultdict(list)
    top_level_entries: list[FuncEntry] = []

    # Track which functions exist in modules (for dedup of top-level re-exports).
    module_funcs: dict[str, str] = {}  # func_name → module_name

    # First pass: collect module entries (depth 3+).
    for entry in lib_entries:
        path = entry["meta"]["path"]
        if len(path) < 3:
            continue

        module_name = path[1]
        if module_name in SKIP_MODULES:
            continue

        func_name = path[-1]
        sig = entry["meta"].get("signature")
        desc = extract_description(entry.get("content"))

        func = FuncEntry(
            name=func_name,
            module=module_name,
            path=path,
            signature=sig,
            description=desc,
        )

        # Manual overrides take priority over noogle translations (some
        # noogle sigs translate but are semantically wrong, e.g. findFirst).
        override = MANUAL_OVERRIDES.get((module_name, func_name))
        if override:
            func.tix_sig = override
        elif sig:
            result = translate_signature(sig)
            func.tix_sig = result.tix_sig
            func.needs_review = result.needs_review
            func.review_reason = result.reason

        module_entries[module_name].append(func)
        module_funcs[func_name] = module_name

    # Second pass: collect top-level entries (depth 2).
    for entry in lib_entries:
        path = entry["meta"]["path"]
        if len(path) != 2:
            continue

        func_name = path[1]
        sig = entry["meta"].get("signature")
        desc = extract_description(entry.get("content"))

        func = FuncEntry(
            name=func_name,
            module=None,
            path=path,
            signature=sig,
            description=desc,
        )

        override = MANUAL_OVERRIDES.get((None, func_name))
        if override:
            func.tix_sig = override
        elif sig:
            result = translate_signature(sig)
            func.tix_sig = result.tix_sig
            func.needs_review = result.needs_review
            func.review_reason = result.reason

        top_level_entries.append(func)

    return module_entries, top_level_entries


# =============================================================================
# .tix output generation
# =============================================================================


def format_doc_comment(desc: str, indent: str) -> str:
    """Format a description as a .tix doc comment (## lines)."""
    # Wrap to fit within the doc width.
    max_width = DOC_WIDTH - len(indent) - 3  # "## " prefix
    wrapped = textwrap.fill(desc, width=max_width)
    lines = wrapped.split("\n")
    return "\n".join(f"{indent}## {line}" for line in lines)


def format_val_decl(func: FuncEntry, indent: str) -> str:
    """Format a single val declaration with optional doc comment.

    Only emits entries that have a translatable signature. Functions without
    signatures are omitted to keep the file focused on what's useful for
    type checking.
    """
    if not func.tix_sig:
        return ""

    lines = []
    if func.description:
        lines.append(format_doc_comment(func.description, indent))

    lines.append(f"{indent}val {func.name} :: {func.tix_sig};")
    return "\n".join(lines)


def format_manual_module(
    name: str,
    entries: list[tuple[str, str, str | None]],
    submodules: dict[str, list[tuple[str, str, str | None]]],
    indent: str,
) -> str:
    """Format a manually-maintained module block with optional submodules.

    Each entry is (val_name, type_signature, doc_comment_or_None).
    """
    inner = indent + "  "
    lines = [f"\n{indent}module {name} {{"]
    for val_name, sig, doc in entries:
        if doc:
            lines.append(format_doc_comment(doc, inner))
        lines.append(f"{inner}val {val_name} :: {sig};")
    for sub_name, sub_entries in submodules.items():
        sub_inner = inner + "  "
        lines.append(f"\n{inner}module {sub_name} {{")
        for val_name, sig, doc in sub_entries:
            if doc:
                lines.append(format_doc_comment(doc, sub_inner))
            lines.append(f"{sub_inner}val {val_name} :: {sig};")
        lines.append(f"{inner}}}")
    lines.append(f"{indent}}}")
    return "\n".join(lines)


def generate_tix(
    module_entries: dict[str, list[FuncEntry]],
    top_level_entries: list[FuncEntry],
) -> str:
    """Generate the complete lib.tix file content."""
    out = []

    # Header.
    out.append(
        """\
# =============================================================================
# nixpkgs lib stubs for Tix  (auto-generated from noogle data)
# =============================================================================
#
# Type declarations for nixpkgs library functions.
# Generated by scripts/gen_lib_stubs.py from noogle.dev data.
#
# Embedded into the binary at compile time and loaded by default.
# Use --no-default-stubs to disable, or --stubs to load additional files.
#
# To regenerate:
#   python3 scripts/gen_lib_stubs.py > stubs/lib.tix"""
    )

    # Top-level type aliases (kept from original).
    out.append(
        """
# ---------------------------------------------------------------------------
# Top-level types
# ---------------------------------------------------------------------------

type Derivation = {
  name: string,
  pname: string,
  version: string,
  type: string,
  outPath: string,
  drvPath: string,
  system: string,
  builder: path | string,
  args: [string],
  outputs: [string],
  meta: { ... },
  ...
};

# Opaque type representing a set of local files.
type FileSet = { ... };

# Opaque type representing a NixOS option type descriptor (e.g. types.str).
type OptionType = { ... };"""
    )

    # pkgs module (kept from original — not in noogle data).
    out.append(
        """
# ---------------------------------------------------------------------------
# pkgs module — creates the "Pkgs" type alias
# ---------------------------------------------------------------------------

module pkgs {

  # mkDerivation accepts either an attrset or a function (finalAttrs: { ... })
  val mkDerivation :: ({ name: string, ... } | { ... } -> { name: string, ... }) -> Derivation;

  val lib :: Lib;

  module stdenv {
    # mkDerivation accepts either an attrset or a function (finalAttrs: { ... })
    val mkDerivation :: ({ name: string, ... } | { ... } -> { name: string, ... }) -> Derivation;
    val cc :: Derivation;
    val shell :: path;
    val isLinux :: bool;
    val isDarwin :: bool;
    val hostPlatform :: { system: string, isLinux: bool, isDarwin: bool, isx86_64: bool, isAarch64: bool, ... };
    val buildPlatform :: { system: string, isLinux: bool, isDarwin: bool, ... };
    val targetPlatform :: { system: string, isLinux: bool, isDarwin: bool, ... };
  }

  # Fetchers — use open attrsets so both `hash` and `sha256` work
  val fetchurl :: { url: string, ... } -> Derivation;
  val fetchFromGitHub :: { owner: string, repo: string, rev: string, ... } -> Derivation;
  val fetchFromGitLab :: { owner: string, repo: string, rev: string, ... } -> Derivation;
  val fetchgit :: { url: string, rev: string, ... } -> Derivation;
  val fetchzip :: { url: string, ... } -> Derivation;
  val fetchpatch :: { url: string, ... } -> Derivation;

  # Common build tools available in scope
  val runCommand :: string -> { ... } -> string -> Derivation;
  val writeText :: string -> string -> Derivation;
  val writeShellScript :: string -> string -> Derivation;
  val writeShellScriptBin :: string -> string -> Derivation;
  val writeShellApplication :: { name: string, text: string, ... } -> Derivation;
  val symlinkJoin :: { name: string, paths: [Derivation | string], ... } -> Derivation;
  val mkShell :: { ... } -> Derivation;
  val mkShellNoCC :: { ... } -> Derivation;

  # callPackage accepts a function or a path, and can return any type
  val callPackage :: (({ ... } -> a) | path) -> { ... } -> a;
}"""
    )

    # lib module.
    out.append(
        """
# ---------------------------------------------------------------------------
# lib module — creates the "Lib" type alias
# ---------------------------------------------------------------------------

module lib {"""
    )

    # Sort modules for deterministic output.
    # Put well-known modules first in a logical order.
    MODULE_ORDER = [
        "trivial",
        "fixedPoints",
        "attrsets",
        "lists",
        "strings",
        "debug",
        "options",
        "modules",
        "types",
        "customisation",
        "asserts",
        "fileset",
        "filesystem",
        "path",
        "sources",
        "versions",
        "meta",
        "generators",
        "gvariant",
        "derivations",
        "cli",
        "fetchers",
        "network",
    ]

    # Emit submodules.
    ordered_modules = []
    seen = set()
    for mod in MODULE_ORDER:
        if mod in module_entries:
            ordered_modules.append(mod)
            seen.add(mod)
    for mod in sorted(module_entries.keys()):
        if mod not in seen:
            ordered_modules.append(mod)

    for mod_name in ordered_modules:
        entries = module_entries[mod_name]
        # Sort entries alphabetically.
        entries.sort(key=lambda e: e.name)
        # Deduplicate by name (keep the one with a signature).
        seen_names: dict[str, FuncEntry] = {}
        for e in entries:
            if e.name not in seen_names or (e.tix_sig and not seen_names[e.name].tix_sig):
                seen_names[e.name] = e
        entries = list(seen_names.values())
        entries.sort(key=lambda e: e.name)

        # Only emit module if we have at least one entry with something to say.
        decls = [format_val_decl(e, "    ") for e in entries]
        decls = [d for d in decls if d]
        if not decls:
            continue

        out.append(f"\n  module {mod_name} {{")
        out.append("\n".join(decls))
        out.append("  }")

    # Types module — manually maintained because lib.types contains opaque
    # values (not functions with translatable noogle signatures) and nested
    # submodules like types.ints. Data lives in MANUAL_TYPES_ENTRIES and
    # MANUAL_TYPES_SUBMODULES at the top of this file.
    out.append(format_manual_module(
        "types", MANUAL_TYPES_ENTRIES, MANUAL_TYPES_SUBMODULES, indent="  ",
    ))

    # Top-level re-exports and functions that only exist at lib.X level.
    # Track which names are already in submodules.
    module_func_names: set[str] = set()
    for entries in module_entries.values():
        for e in entries:
            module_func_names.add(e.name)

    # Separate top-level entries into:
    # 1. Re-exports (also in a submodule) — just emit the val
    # 2. Top-level only — full doc + val
    reexports = []
    top_only = []
    for func in top_level_entries:
        if func.name in module_func_names:
            reexports.append(func)
        else:
            top_only.append(func)

    # Emit top-level only functions.
    if top_only:
        top_only.sort(key=lambda e: e.name)
        # Deduplicate.
        seen_names = {}
        for e in top_only:
            if e.name not in seen_names or (e.tix_sig and not seen_names[e.name].tix_sig):
                seen_names[e.name] = e
        top_only = sorted(seen_names.values(), key=lambda e: e.name)

        top_decls = [format_val_decl(e, "  ") for e in top_only if e.tix_sig]
        if top_decls:
            out.append("\n  # Top-level lib functions")
            out.append("\n".join(top_decls))

    # Emit re-exports (just the val declarations, no docs).
    if reexports:
        reexports.sort(key=lambda e: e.name)
        seen_names = {}
        for e in reexports:
            if e.name not in seen_names or (e.tix_sig and not seen_names[e.name].tix_sig):
                seen_names[e.name] = e
        reexports = sorted(seen_names.values(), key=lambda e: e.name)

        reexport_decls = [f"  val {e.name} :: {e.tix_sig};" for e in reexports if e.tix_sig]
        if reexport_decls:
            out.append(
                "\n  # Re-exports — nixpkgs lib re-exports submodule functions at the top level"
            )
            out.append("\n".join(reexport_decls))

    out.append("}")  # close module lib

    return "\n".join(out) + "\n"


# =============================================================================
# Main
# =============================================================================


def main():
    print("Loading noogle data...", file=sys.stderr)
    data = load_noogle_data()
    print(f"  {len(data)} total entries", file=sys.stderr)

    module_entries, top_level_entries = process_entries(data)

    total_module_funcs = sum(len(v) for v in module_entries.values())
    with_sig = sum(1 for v in module_entries.values() for e in v if e.tix_sig)
    top_with_sig = sum(1 for e in top_level_entries if e.tix_sig)
    print(
        f"  {len(module_entries)} modules, {total_module_funcs} module functions ({with_sig} with translated sigs)",
        file=sys.stderr,
    )
    print(
        f"  {len(top_level_entries)} top-level entries ({top_with_sig} with translated sigs)",
        file=sys.stderr,
    )

    output = generate_tix(module_entries, top_level_entries)
    print(output, end="")

    # Stats.
    val_count = output.count("\nval ") + output.count("\n  val ") + output.count("\n    val ")
    print(f"  Generated {val_count} val declarations", file=sys.stderr)


if __name__ == "__main__":
    main()
