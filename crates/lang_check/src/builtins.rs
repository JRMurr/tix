// ==============================================================================
// Builtin Type Synthesis
// ==============================================================================
//
// Each builtin reference synthesizes its type *fresh* (new `new_var()` calls
// each time). This naturally gives polymorphic behavior without needing
// pre-generalization or extrusion — the vars are at the current level, and if
// the builtin is bound in a `let`, normal SCC generalization handles polymorphism.

use std::collections::{BTreeMap, BTreeSet};

use lang_ty::{AttrSetTy, PrimitiveTy, Ty};
use smol_str::SmolStr;

use super::{CheckCtx, InferenceError, TyId};

/// All builtin names that should appear as fields in the `builtins` attrset.
const ALL_BUILTIN_NAMES: &[&str] = &[
    // Priority 1 — type predicates & simple functions
    "isAttrs",
    "isBool",
    "isFloat",
    "isFunction",
    "isInt",
    "isList",
    "isNull",
    "isPath",
    "isString",
    "typeOf",
    "head",
    "tail",
    "length",
    "elemAt",
    "elem",
    "stringLength",
    "ceil",
    "floor",
    "toString",
    "toJSON",
    "fromJSON",
    "fromTOML",
    "seq",
    "deepSeq",
    "trace",
    "throw",
    "abort",
    "import",
    "scopedImport",
    "attrNames",
    "hasAttr",
    "getEnv",
    "pathExists",
    "readFile",
    // String operations
    "substring",
    "split",
    "match",
    "replaceStrings",
    "concatStringsSep",
    "compareVersions",
    "parseDrvName",
    "unsafeDiscardStringContext",
    "appendContext",
    // Attrset access
    "getAttr",
    // Priority 2 — higher-order list/attrset operations
    "map",
    "filter",
    "foldl'",
    "genList",
    "concatLists",
    "concatMap",
    "sort",
    "all",
    "any",
    "partition",
    "groupBy",
    "mapAttrs",
    "tryEval",
    "functionArgs",
    "listToAttrs",
    "removeAttrs",
    // Priority 3 — value constants
    "langVersion",
    "nixVersion",
    "currentSystem",
    "currentTime",
    "storeDir",
    "storePath",
];

/// Build a fresh builtin type from a mini type expression.
///
/// Variables declared before `=>` get one `new_var()` each.
/// Right-associative `->` for curried lambdas.
///
/// ```text
/// synth_ty!(self; a, b => (a -> b) -> [a] -> [b])
/// //        ^^^^  ^^^^    ^^^^^^^^^^^^^^^^^^^^^^^^
/// //        ctx   vars    type expression
/// ```
macro_rules! synth_ty {
    // Entry: declare vars, parse type, wrap in Ok
    ($ctx:expr; $($var:ident),+ => $($ty:tt)+) => {{
        $(let $var = $ctx.new_var();)*
        Ok(synth_ty!(@ty $ctx; $($ty)+))
    }};
    // Entry: no vars needed
    ($ctx:expr; => $($ty:tt)+) => {
        Ok(synth_ty!(@ty $ctx; $($ty)+))
    };

    // Lambda (right-associative): first tt, then ->, then rest
    (@ty $ctx:expr; $param:tt -> $($rest:tt)+) => {{
        let param = synth_ty!(@ty $ctx; $param);
        let body = synth_ty!(@ty $ctx; $($rest)+);
        $ctx.alloc_concrete(Ty::Lambda { param, body })
    }};
    // Parenthesized group
    (@ty $ctx:expr; ($($inner:tt)+)) => {
        synth_ty!(@ty $ctx; $($inner)+)
    };
    // List
    (@ty $ctx:expr; [$($inner:tt)+]) => {{
        let elem = synth_ty!(@ty $ctx; $($inner)+);
        $ctx.alloc_concrete(Ty::List(elem))
    }};
    // Open empty attrset
    (@ty $ctx:expr; { .. }) => {
        $ctx.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(), dyn_ty: None, open: true,
            optional_fields: BTreeSet::new(),
        }))
    };
    // Open attrset with dynamic field type
    (@ty $ctx:expr; { _ : $($inner:tt)+ }) => {{
        let dyn_ty = synth_ty!(@ty $ctx; $($inner)+);
        $ctx.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(), dyn_ty: Some(dyn_ty), open: true,
            optional_fields: BTreeSet::new(),
        }))
    }};
    // Primitives
    (@ty $ctx:expr; Bool) => { $ctx.alloc_prim(PrimitiveTy::Bool) };
    (@ty $ctx:expr; Int) => { $ctx.alloc_prim(PrimitiveTy::Int) };
    (@ty $ctx:expr; Float) => { $ctx.alloc_prim(PrimitiveTy::Float) };
    (@ty $ctx:expr; String) => { $ctx.alloc_prim(PrimitiveTy::String) };
    (@ty $ctx:expr; Null) => { $ctx.alloc_prim(PrimitiveTy::Null) };
    (@ty $ctx:expr; Path) => { $ctx.alloc_prim(PrimitiveTy::Path) };
    (@ty $ctx:expr; Number) => { $ctx.alloc_prim(PrimitiveTy::Number) };
    // Variable reference (catch-all — must be last)
    (@ty $ctx:expr; $var:ident) => { $var };
}

impl CheckCtx<'_> {
    /// Synthesize the type for a named builtin. Returns fresh type vars
    /// for polymorphic builtins so each reference is independent.
    pub(crate) fn synthesize_builtin(&mut self, name: &str) -> Result<TyId, InferenceError> {
        match name {
            // =================================================================
            // Priority 1 — Type predicates & simple functions
            // =================================================================

            // a -> bool
            "isAttrs" | "isBool" | "isFloat" | "isFunction" | "isInt" | "isList" | "isNull"
            | "isPath" | "isString" | "pathExists" => synth_ty!(self; a => a -> Bool),

            // a -> string
            "typeOf" | "toString" | "toJSON" | "readFile" => synth_ty!(self; a => a -> String),

            // string -> a
            "fromJSON" | "fromTOML" | "throw" | "abort" => synth_ty!(self; a => String -> a),

            "head" => synth_ty!(self; a => [a] -> a),
            "tail" => synth_ty!(self; a => [a] -> [a]),
            "length" => synth_ty!(self; a => [a] -> Int),
            "elemAt" => synth_ty!(self; a => [a] -> Int -> a),
            "elem" => synth_ty!(self; a => a -> [a] -> Bool),
            "stringLength" => synth_ty!(self; => String -> Int),
            "getEnv" => synth_ty!(self; => String -> String),
            "ceil" | "floor" => synth_ty!(self; => Float -> Int),
            "seq" | "deepSeq" | "trace" => synth_ty!(self; a, b => a -> b -> b),
            "import" => synth_ty!(self; a, b => a -> b),
            // scopedImport takes an attrset scope and a path, returns the import result.
            "scopedImport" => synth_ty!(self; a, b, c => a -> b -> c),

            // =================================================================
            // String operations
            // =================================================================
            "substring" => synth_ty!(self; => Int -> Int -> String -> String),
            // split returns alternating strings and lists of captured groups;
            // we use [a] since unions aren't available during inference.
            "split" => synth_ty!(self; a => String -> String -> [a]),
            // match returns null (no match) or [string] (captured groups);
            // we use a since unions aren't available during inference.
            "match" => synth_ty!(self; a => String -> String -> a),
            "replaceStrings" => synth_ty!(self; => [String] -> [String] -> String -> String),
            "concatStringsSep" => synth_ty!(self; => String -> [String] -> String),
            "compareVersions" => synth_ty!(self; => String -> String -> Int),
            "parseDrvName" => self.synth_parse_drv_name(),
            "unsafeDiscardStringContext" => synth_ty!(self; => String -> String),
            "appendContext" => synth_ty!(self; => String -> {..} -> String),

            // =================================================================
            // {..} builtins
            // =================================================================
            "attrNames" => synth_ty!(self; => {..} -> [String]),
            "hasAttr" => synth_ty!(self; => String -> {..} -> Bool),
            "getAttr" => synth_ty!(self; a => String -> { _ : a } -> a),
            "removeAttrs" => synth_ty!(self; => {..} -> [String] -> {..}),

            // =================================================================
            // Priority 2 — Higher-order list/attrset operations
            // =================================================================
            "map" => synth_ty!(self; a, b => (a -> b) -> [a] -> [b]),
            "filter" => synth_ty!(self; a => (a -> Bool) -> [a] -> [a]),
            "foldl'" => synth_ty!(self; a, b => (a -> b -> a) -> a -> [b] -> a),
            "genList" => synth_ty!(self; a => (Int -> a) -> Int -> [a]),
            "concatLists" => synth_ty!(self; a => [[a]] -> [a]),
            "concatMap" => synth_ty!(self; a, b => (a -> [b]) -> [a] -> [b]),
            "sort" => synth_ty!(self; a => (a -> a -> Bool) -> [a] -> [a]),
            "all" | "any" => synth_ty!(self; a => (a -> Bool) -> [a] -> Bool),

            // {_ : ty} builtins
            "groupBy" => synth_ty!(self; a => (a -> String) -> [a] -> { _ : [a] }),
            "mapAttrs" => synth_ty!(self; a, b => (String -> a -> b) -> { _ : a } -> { _ : b }),
            "functionArgs" => synth_ty!(self; a, b => (a -> b) -> { _ : Bool }),

            // Complex attrset return types — named fields need manual construction.
            "partition" => self.synth_partition(),
            "tryEval" => self.synth_try_eval(),
            "listToAttrs" => self.synth_list_to_attrs(),

            // =================================================================
            // Priority 3 — Value constants
            // =================================================================
            "langVersion" | "currentTime" => Ok(self.alloc_prim(PrimitiveTy::Int)),
            "nixVersion" | "currentSystem" | "storeDir" => Ok(self.alloc_prim(PrimitiveTy::String)),
            "storePath" => synth_ty!(self; => Path -> Path),

            // Language keywords — resolved as builtins so they bypass `with` scopes.
            "true" | "false" => Ok(self.alloc_prim(PrimitiveTy::Bool)),
            "null" => Ok(self.alloc_prim(PrimitiveTy::Null)),

            // Unknown builtins get a fresh type variable — graceful degradation.
            _ => Ok(self.new_var()),
        }
    }

    /// Synthesize the `builtins` attrset containing all known builtins as fields.
    pub(crate) fn synth_builtins_attrset(&mut self) -> Result<TyId, InferenceError> {
        let mut fields = BTreeMap::new();
        for &name in ALL_BUILTIN_NAMES {
            let ty = self.synthesize_builtin(name)?;
            fields.insert(SmolStr::from(name), ty);
        }
        // open: true — builtins we don't model yet are still accessible
        // (as fresh vars via dyn_ty).
        let dyn_var = self.new_var();
        Ok(self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields,
            dyn_ty: Some(dyn_var),
            open: true,
            optional_fields: BTreeSet::new(),
        })))
    }

    // =========================================================================
    // Manual signature builders (named attrset fields)
    // =========================================================================

    /// string -> {"name": string, "version": string}
    fn synth_parse_drv_name(&mut self) -> Result<TyId, InferenceError> {
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let mut fields = BTreeMap::new();
        fields.insert(SmolStr::from("name"), string_ty);
        fields.insert(SmolStr::from("version"), string_ty);
        let result = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields,
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
        }));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: string_ty,
            body: result,
        }))
    }

    /// (a -> bool) -> [a] -> {"right": [a], "wrong": [a]}
    fn synth_partition(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let pred = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: bool_ty,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let mut result_fields = BTreeMap::new();
        result_fields.insert(SmolStr::from("right"), list_a);
        result_fields.insert(SmolStr::from("wrong"), list_a);
        let result_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: result_fields,
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
        }));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: result_attr,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: pred,
            body: inner,
        }))
    }

    /// a -> {"success": bool, "value": a}
    fn synth_try_eval(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let mut fields = BTreeMap::new();
        fields.insert(SmolStr::from("success"), bool_ty);
        fields.insert(SmolStr::from("value"), a);
        let result = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields,
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
        }));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: result,
        }))
    }

    /// [{"name": string, "value": a}] -> {_ : a}
    fn synth_list_to_attrs(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let mut elem_fields = BTreeMap::new();
        elem_fields.insert(SmolStr::from("name"), string_ty);
        elem_fields.insert(SmolStr::from("value"), a);
        let elem_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: elem_fields,
            dyn_ty: None,
            open: false,
            optional_fields: BTreeSet::new(),
        }));
        let list_elems = self.alloc_concrete(Ty::List(elem_attr));
        let result = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: Some(a),
            open: true,
            optional_fields: BTreeSet::new(),
        }));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_elems,
            body: result,
        }))
    }
}
