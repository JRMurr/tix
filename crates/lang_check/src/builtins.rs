// ==============================================================================
// Builtin Type Synthesis
// ==============================================================================
//
// Each builtin reference synthesizes its type *fresh* (new `new_var()` calls
// each time). This naturally gives polymorphic behavior without needing
// pre-generalization or extrusion — the vars are at the current level, and if
// the builtin is bound in a `let`, normal SCC generalization handles polymorphism.

use std::collections::BTreeMap;

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
    "attrNames",
    "hasAttr",
    "getEnv",
    "pathExists",
    "readFile",
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
];

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
            | "isPath" | "isString" | "pathExists" => self.synth_a_to_bool(),

            // a -> string
            "typeOf" | "toString" | "toJSON" | "readFile" => self.synth_a_to_string(),

            // string -> a
            "fromJSON" | "fromTOML" => self.synth_string_to_a(),

            // [a] -> a
            "head" => self.synth_head(),

            // [a] -> [a]
            "tail" => self.synth_tail(),

            // [a] -> int
            "length" => self.synth_list_to_int(),

            // [a] -> int -> a
            "elemAt" => self.synth_elem_at(),

            // a -> [a] -> bool
            "elem" => self.synth_elem(),

            // string -> int
            "stringLength" | "getEnv" => self.synth_string_to_int_or_string(name),

            // float -> int
            "ceil" | "floor" => self.synth_float_to_int(),

            // a -> b -> b
            "seq" | "deepSeq" | "trace" => self.synth_a_b_to_b(),

            // string -> a
            "throw" | "abort" => self.synth_string_to_a(),

            // a -> b
            "import" | "scopedImport" => self.synth_a_to_b(),

            // {..} -> [string]
            "attrNames" => self.synth_attr_names(),

            // string -> {..} -> bool
            "hasAttr" => self.synth_has_attr(),

            // =================================================================
            // Priority 2 — Higher-order list/attrset operations
            // =================================================================

            // (a -> b) -> [a] -> [b]
            "map" => self.synth_map(),

            // (a -> bool) -> [a] -> [a]
            "filter" => self.synth_filter(),

            // (a -> b -> a) -> a -> [b] -> a
            "foldl'" => self.synth_foldl(),

            // (int -> a) -> int -> [a]
            "genList" => self.synth_gen_list(),

            // [[a]] -> [a]
            "concatLists" => self.synth_concat_lists(),

            // (a -> [b]) -> [a] -> [b]
            "concatMap" => self.synth_concat_map(),

            // (a -> a -> bool) -> [a] -> [a]
            "sort" => self.synth_sort(),

            // (a -> bool) -> [a] -> bool
            "all" | "any" => self.synth_all_any(),

            // (a -> bool) -> [a] -> {"right": [a], "wrong": [a]}
            "partition" => self.synth_partition(),

            // (a -> string) -> [a] -> {_ : [a]}
            "groupBy" => self.synth_group_by(),

            // (string -> a -> b) -> {_ : a} -> {_ : b}
            "mapAttrs" => self.synth_map_attrs(),

            // a -> {"success": bool, "value": a}
            "tryEval" => self.synth_try_eval(),

            // (a -> b) -> {_ : bool}
            "functionArgs" => self.synth_function_args(),

            // [{"name": string, "value": a}] -> {_ : a}
            "listToAttrs" => self.synth_list_to_attrs(),

            // {..} -> [string] -> {..}
            "removeAttrs" => self.synth_remove_attrs(),

            // =================================================================
            // Priority 3 — Value constants
            // =================================================================
            "langVersion" | "currentTime" => Ok(self.alloc_prim(PrimitiveTy::Int)),
            "nixVersion" | "currentSystem" | "storeDir" => {
                Ok(self.alloc_prim(PrimitiveTy::String))
            }

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
        })))
    }

    // =========================================================================
    // Signature builders
    // =========================================================================

    /// a -> bool
    fn synth_a_to_bool(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: bool_ty,
        }))
    }

    /// a -> string
    fn synth_a_to_string(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: string_ty,
        }))
    }

    /// string -> a
    fn synth_string_to_a(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        Ok(self.alloc_concrete(Ty::Lambda {
            param: string_ty,
            body: a,
        }))
    }

    /// [a] -> a
    fn synth_head(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let list_a = self.alloc_concrete(Ty::List(a));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: a,
        }))
    }

    /// [a] -> [a]
    fn synth_tail(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let list_a = self.alloc_concrete(Ty::List(a));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: list_a,
        }))
    }

    /// [a] -> int
    fn synth_list_to_int(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let list_a = self.alloc_concrete(Ty::List(a));
        let int_ty = self.alloc_prim(PrimitiveTy::Int);
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: int_ty,
        }))
    }

    /// [a] -> int -> a
    fn synth_elem_at(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let list_a = self.alloc_concrete(Ty::List(a));
        let int_ty = self.alloc_prim(PrimitiveTy::Int);
        let inner = self.alloc_concrete(Ty::Lambda {
            param: int_ty,
            body: a,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: inner,
        }))
    }

    /// a -> [a] -> bool
    fn synth_elem(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let list_a = self.alloc_concrete(Ty::List(a));
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: bool_ty,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: inner,
        }))
    }

    /// Dispatches between `string -> int` (stringLength) and `string -> string` (getEnv).
    fn synth_string_to_int_or_string(
        &mut self,
        name: &str,
    ) -> Result<TyId, InferenceError> {
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let ret = match name {
            "stringLength" => self.alloc_prim(PrimitiveTy::Int),
            "getEnv" => self.alloc_prim(PrimitiveTy::String),
            _ => unreachable!(),
        };
        Ok(self.alloc_concrete(Ty::Lambda {
            param: string_ty,
            body: ret,
        }))
    }

    /// float -> int
    fn synth_float_to_int(&mut self) -> Result<TyId, InferenceError> {
        let float_ty = self.alloc_prim(PrimitiveTy::Float);
        let int_ty = self.alloc_prim(PrimitiveTy::Int);
        Ok(self.alloc_concrete(Ty::Lambda {
            param: float_ty,
            body: int_ty,
        }))
    }

    /// a -> b -> b
    fn synth_a_b_to_b(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        let inner = self.alloc_concrete(Ty::Lambda { param: b, body: b });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: inner,
        }))
    }

    /// a -> b
    fn synth_a_to_b(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: b,
        }))
    }

    /// {..} -> [string]
    fn synth_attr_names(&mut self) -> Result<TyId, InferenceError> {
        let open_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: None,
            open: true,
        }));
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let list_string = self.alloc_concrete(Ty::List(string_ty));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: open_attr,
            body: list_string,
        }))
    }

    /// string -> {..} -> bool
    fn synth_has_attr(&mut self) -> Result<TyId, InferenceError> {
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let open_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: None,
            open: true,
        }));
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let inner = self.alloc_concrete(Ty::Lambda {
            param: open_attr,
            body: bool_ty,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: string_ty,
            body: inner,
        }))
    }

    /// (a -> b) -> [a] -> [b]
    fn synth_map(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        let fn_ty = self.alloc_concrete(Ty::Lambda { param: a, body: b });
        let list_a = self.alloc_concrete(Ty::List(a));
        let list_b = self.alloc_concrete(Ty::List(b));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: list_b,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: fn_ty,
            body: inner,
        }))
    }

    /// (a -> bool) -> [a] -> [a]
    fn synth_filter(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let pred = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: bool_ty,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: list_a,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: pred,
            body: inner,
        }))
    }

    /// (a -> b -> a) -> a -> [b] -> a
    fn synth_foldl(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        let step_inner = self.alloc_concrete(Ty::Lambda { param: b, body: a });
        let step = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: step_inner,
        });
        let list_b = self.alloc_concrete(Ty::List(b));
        let inner2 = self.alloc_concrete(Ty::Lambda {
            param: list_b,
            body: a,
        });
        let inner1 = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: inner2,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: step,
            body: inner1,
        }))
    }

    /// (int -> a) -> int -> [a]
    fn synth_gen_list(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let int_ty = self.alloc_prim(PrimitiveTy::Int);
        let gen_fn = self.alloc_concrete(Ty::Lambda {
            param: int_ty,
            body: a,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: int_ty,
            body: list_a,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: gen_fn,
            body: inner,
        }))
    }

    /// [[a]] -> [a]
    fn synth_concat_lists(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let list_a = self.alloc_concrete(Ty::List(a));
        let list_list_a = self.alloc_concrete(Ty::List(list_a));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_list_a,
            body: list_a,
        }))
    }

    /// (a -> [b]) -> [a] -> [b]
    fn synth_concat_map(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        let list_b = self.alloc_concrete(Ty::List(b));
        let fn_ty = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: list_b,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: list_b,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: fn_ty,
            body: inner,
        }))
    }

    /// (a -> a -> bool) -> [a] -> [a]
    fn synth_sort(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let cmp_inner = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: bool_ty,
        });
        let cmp = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: cmp_inner,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: list_a,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: cmp,
            body: inner,
        }))
    }

    /// (a -> bool) -> [a] -> bool
    fn synth_all_any(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let pred = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: bool_ty,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: bool_ty,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: pred,
            body: inner,
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

    /// (a -> string) -> [a] -> {_ : [a]}
    fn synth_group_by(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let key_fn = self.alloc_concrete(Ty::Lambda {
            param: a,
            body: string_ty,
        });
        let list_a = self.alloc_concrete(Ty::List(a));
        let result_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: Some(list_a),
            open: true,
        }));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_a,
            body: result_attr,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: key_fn,
            body: inner,
        }))
    }

    /// (string -> a -> b) -> {_ : a} -> {_ : b}
    fn synth_map_attrs(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let fn_inner = self.alloc_concrete(Ty::Lambda { param: a, body: b });
        let fn_ty = self.alloc_concrete(Ty::Lambda {
            param: string_ty,
            body: fn_inner,
        });
        let attr_a = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: Some(a),
            open: true,
        }));
        let attr_b = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: Some(b),
            open: true,
        }));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: attr_a,
            body: attr_b,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: fn_ty,
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
        }));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: a,
            body: result,
        }))
    }

    /// (a -> b) -> {_ : bool}
    fn synth_function_args(&mut self) -> Result<TyId, InferenceError> {
        let a = self.new_var();
        let b = self.new_var();
        let fn_ty = self.alloc_concrete(Ty::Lambda { param: a, body: b });
        let bool_ty = self.alloc_prim(PrimitiveTy::Bool);
        let result = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: Some(bool_ty),
            open: true,
        }));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: fn_ty,
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
        }));
        let list_elems = self.alloc_concrete(Ty::List(elem_attr));
        let result = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: Some(a),
            open: true,
        }));
        Ok(self.alloc_concrete(Ty::Lambda {
            param: list_elems,
            body: result,
        }))
    }

    /// {..} -> [string] -> {..}
    fn synth_remove_attrs(&mut self) -> Result<TyId, InferenceError> {
        let open_attr = self.alloc_concrete(Ty::AttrSet(AttrSetTy {
            fields: BTreeMap::new(),
            dyn_ty: None,
            open: true,
        }));
        let string_ty = self.alloc_prim(PrimitiveTy::String);
        let list_string = self.alloc_concrete(Ty::List(string_ty));
        let inner = self.alloc_concrete(Ty::Lambda {
            param: list_string,
            body: open_attr,
        });
        Ok(self.alloc_concrete(Ty::Lambda {
            param: open_attr,
            body: inner,
        }))
    }
}
