import E213.Term.Tree
import E213.Theory.Raw.Core

/-!
# Theory.Raw.CoResidue — a structural escape: the infinite complete self-pointing

`MuNuMirror` gave the escape its *finite depth shadow* (depths cofinal, no finite Raw caps
the ascent).  This file gives a *structural* witness, one step closer to the open νF (the
final `F`-coalgebra): a concrete carrier of (possibly infinite) self-pointing trees, into
which the finite Raw embeds **non-surjectively**, with a **named infinite inhabitant** that
has genuine infinite descent.

Model (the path-function / coalgebra route).  A self-pointing tree is presented by where its
internal (branch) nodes are: `CoShape := List Bool → Bool`, with `s p = true` meaning "the
node at path `p` is a branch".  This is an `F`-coalgebra carrier — `coOut` reads the root
shape and the two subtrees (`coLeft`, `coRight`).

  * **Embedding** `toShape : Tree → CoShape` — a finite tree as a shape: atoms are leaves
    everywhere, a slash is a branch at the root with the two children as subtrees.  Every
    finite tree has a **leaf path** (`tree_has_leaf_path`).

  * **The infinite inhabitant** `allBranch := fun _ => true` — a branch at *every* path: it
    has **no leaf** (`allBranch_no_leaf`) and is its own left subtree
    (`allBranch_coLeft_self`), so its `coOut`-descent never terminates — the completed
    infinite self-pointing.

  * **The structural escape** `raw_ne_allBranch` — `toShape r.val ≠ allBranch` for every Raw
    `r`: no finite Raw is the infinite tree.  This is the escape given *structurally* (a
    named inhabitant outside the image with genuine infinite descent), not via `depth` or
    predicates.

Honest scope: this is an **emulation**, not Lean-native coinduction — `CoShape` is the full
function space, not the well-formed-cotree subtype, and `toShape` is not claimed injective
here (the escape needs only non-surjectivity).  It is a structural shadow richer than the
depth one, still not the residue itself (which stays outside every view).  The `≠` uses a
pointwise difference, so no `funext`.  All zero-axiom.
-/

namespace E213.Theory.Raw.CoResidue

open E213.Term.Internal (Tree)
open E213.Theory (Raw)

/-- A (possibly infinite) self-pointing tree, presented by its branch-node paths:
    `s p = true` iff the node at path `p` is a branch (`false` = leaf / beyond). -/
def CoShape : Type := List Bool → Bool

/-! ## §1 — the coalgebra structure (every co-tree decomposes) -/

/-- The root is a branch? -/
def coIsBranch (s : CoShape) : Bool := s []

/-- The left subtree (paths under the `true` child). -/
def coLeft (s : CoShape) : CoShape := fun p => s (true :: p)

/-- The right subtree (paths under the `false` child). -/
def coRight (s : CoShape) : CoShape := fun p => s (false :: p)

/-- The `F`-coalgebra readout: root shape + the two subtrees. -/
def coOut (s : CoShape) : Bool × CoShape × CoShape := (coIsBranch s, coLeft s, coRight s)

/-! ## §2 — the finite embedding and its leaf paths -/

/-- A finite tree as a shape: atoms are leaves (no branch anywhere), a slash is a branch at
    the root with its two children as subtrees. -/
def toShape : Tree → CoShape
  | Tree.a,         _            => false
  | Tree.b,         _            => false
  | Tree.slash _ _, []           => true
  | Tree.slash x _, (true :: p)  => toShape x p
  | Tree.slash _ y, (false :: p) => toShape y p

/-- ★ **Every finite tree has a leaf path.**  By structural recursion: atoms are leaves at
    the root; a slash inherits a leaf path from its left child. -/
theorem tree_has_leaf_path : ∀ t : Tree, ∃ p : List Bool, toShape t p = false
  | Tree.a         => ⟨[], rfl⟩
  | Tree.b         => ⟨[], rfl⟩
  | Tree.slash x _ =>
      let ⟨p, hp⟩ := tree_has_leaf_path x
      ⟨true :: p, hp⟩

/-! ## §3 — the infinite inhabitant: the complete self-pointing -/

/-- The infinite complete tree: a branch at every path. -/
def allBranch : CoShape := fun _ => true

/-- `allBranch` has **no leaf**: every path is a branch. -/
theorem allBranch_no_leaf (p : List Bool) : allBranch p = true := rfl

/-- `allBranch` is its **own left subtree** (pointwise — no `funext`): peeling a child
    returns the same infinite tree, so its `coOut`-descent never terminates. -/
theorem allBranch_coLeft_self (p : List Bool) : coLeft allBranch p = allBranch p := rfl

/-- `allBranch` is a branch at the root (its descent continues). -/
theorem allBranch_isBranch : coIsBranch allBranch = true := rfl

/-! ## §4 — the structural escape -/

/-- ★★ **No finite tree is the infinite one.**  `toShape t ≠ allBranch`: a finite tree has a
    leaf path where its shape is `false`, but `allBranch` is `true` everywhere.  (Pointwise
    difference ⟹ `≠`; no `funext`.) -/
theorem toShape_ne_allBranch (t : Tree) : toShape t ≠ allBranch := by
  intro h
  obtain ⟨p, hp⟩ := tree_has_leaf_path t
  have e : allBranch p = false := by rw [← h]; exact hp
  exact Bool.noConfusion e

/-- The embedding of a Raw as a self-pointing shape (via its canonical tree). -/
def toShapeRaw (r : Raw) : CoShape := toShape r.val

/-- ★★★ **The infinite complete self-pointing escapes Raw — structurally.**  For every Raw
    `r`, `toShapeRaw r ≠ allBranch`: no finite Raw is the infinite complete tree.  The
    escape given by a *named structural inhabitant* (`allBranch`) outside the image — with
    genuine infinite descent (`allBranch_no_leaf`, `allBranch_coLeft_self`) — richer than the
    depth shadow (`MuNuMirror`), still an emulation of the open νF, still not the residue
    itself. -/
theorem raw_ne_allBranch (r : Raw) : toShapeRaw r ≠ allBranch :=
  toShape_ne_allBranch r.val

/-- ★★★ **The structural escape, bundled.**  The infinite complete self-pointing `allBranch`
    (1) decomposes as a branch with itself as left subtree — infinite `coOut`-descent
    (`allBranch_isBranch`, `allBranch_coLeft_self`, `allBranch_no_leaf`); and (2) is outside
    the image of the finite-Raw embedding (`raw_ne_allBranch`).  A positive structural form
    of the residue's escape: a named co-tree with genuine non-termination, reached by no
    finite Raw. -/
theorem structural_escape :
    (coIsBranch allBranch = true
      ∧ (∀ p, coLeft allBranch p = allBranch p)
      ∧ (∀ p, allBranch p = true))
    ∧ (∀ r : Raw, toShapeRaw r ≠ allBranch) :=
  ⟨⟨allBranch_isBranch, allBranch_coLeft_self, allBranch_no_leaf⟩, raw_ne_allBranch⟩

end E213.Theory.Raw.CoResidue
