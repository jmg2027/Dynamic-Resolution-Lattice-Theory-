//! Internal `Tree` scaffolding — invisible outside `firmware` crate.
//!
//! Mirror of `lean/E213/Firmware/Raw/Core.lean` `Internal.Tree`:
//!
//! ```lean
//! inductive Tree : Type
//!   | a | b
//!   | slash : Tree → Tree → Tree
//! ```
//!
//! Plus `Tree.cmp` (lex on inductive structure) and `Tree.canonical`
//! (slash children must be strictly ordered `<`).  These live here
//! because Lean isolates them in `E213.Firmware.Internal`.

use std::cmp::Ordering;

#[derive(Clone, Eq, PartialEq, Debug)]
pub(crate) enum Tree {
    A,
    B,
    Slash(Box<Tree>, Box<Tree>),
}

impl Tree {
    /// `Tree.cmp` — total order matching Lean's `Internal.Tree.cmp`.
    pub(crate) fn cmp(&self, other: &Tree) -> Ordering {
        use Tree::*;
        match (self, other) {
            (A, A)                 => Ordering::Equal,
            (A, _)                 => Ordering::Less,
            (B, A)                 => Ordering::Greater,
            (B, B)                 => Ordering::Equal,
            (B, Slash(_, _))       => Ordering::Less,
            (Slash(_, _), A)       => Ordering::Greater,
            (Slash(_, _), B)       => Ordering::Greater,
            (Slash(x1, y1), Slash(x2, y2)) => {
                match x1.cmp(x2) {
                    Ordering::Equal => y1.cmp(y2),
                    other_o => other_o,
                }
            }
        }
    }

    /// `canonical` — slash children must satisfy `x < y` strictly.
    /// Currently only used by tests; `Raw::slash` enforces by ordering
    /// children, so canonicality is *constructive*.  Kept for invariant
    /// audits and future debug paths.
    #[allow(dead_code)]
    pub(crate) fn canonical(&self) -> bool {
        match self {
            Tree::A | Tree::B => true,
            Tree::Slash(x, y) => {
                x.canonical() && y.canonical()
                    && matches!(x.cmp(y), Ordering::Less)
            }
        }
    }

    /// `Tree.depth` — Lean: `Internal.Tree.depth`.
    pub(crate) fn depth(&self) -> u64 {
        match self {
            Tree::A | Tree::B => 0,
            Tree::Slash(x, y) => 1 + std::cmp::max(x.depth(), y.depth()),
        }
    }

    /// `Tree.fold` — Lean: `Internal.Tree.fold`.
    pub(crate) fn fold<A: Clone, F: Fn(&A, &A) -> A + ?Sized>(
        &self, fa: A, fb: A, fc: &F,
    ) -> A {
        match self {
            Tree::A => fa,
            Tree::B => fb,
            Tree::Slash(x, y) => {
                let lx = x.fold(fa.clone(), fb.clone(), fc);
                let ly = y.fold(fa, fb, fc);
                fc(&lx, &ly)
            }
        }
    }
}
