//! Stack-guard parameters shared by every recursive AST/type walk in the
//! workspace. Deeply nested input (machine-generated Nix, huge binop chains)
//! would otherwise overflow the stack.

/// Remaining-stack threshold below which a new segment is allocated.
pub const STACK_RED_ZONE: usize = 256 * 1024;

/// Size of each newly allocated stack segment.
pub const STACK_GROW_SIZE: usize = 1024 * 1024;

/// Run `f`, growing the stack when less than [`STACK_RED_ZONE`] remains.
/// Wrap the recursive step of any walk whose depth follows input nesting.
#[inline]
pub fn with_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(STACK_RED_ZONE, STACK_GROW_SIZE, f)
}
