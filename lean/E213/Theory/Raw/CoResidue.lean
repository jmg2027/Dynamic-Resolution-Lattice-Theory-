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

/-! ## §5 — the anamorphism: every coalgebra unfolds into `CoShape`

An `F`-coalgebra is a seed type `X` with `c : X → Bool × X × X` (root-is-branch, left seed,
right seed).  The **anamorphism** `ana c` unfolds any coalgebra into `CoShape` — it walks a
path, branching by the seed's children — and it commutes with the `coOut` projections **by
definition** (`ana_isBranch/coLeft/coRight` are `rfl`).  So every `F`-coalgebra admits an
unfold into `CoShape` (the existence-of-a-coalgebra-morphism half; in categorical gloss,
weak finality — *not* formalised as an object property here, and *not* the uniqueness that
full finality needs).  Both the finite embedding (`toShape = ana treeCoalg`) and the infinite
inhabitant (`allBranch = ana` of the always-branch coalgebra) are anamorphisms — the
difference is whether the seed-coalgebra's unfold has a leaf path (`Tree`, terminates) or is
leaf-free (`allBranch`).

Honest scope: only the **existence** of unfolds (+ three `rfl` commutations) is proven;
*uniqueness* of the unfold (finality proper) needs bisimulation/coinduction and stays open.
And this `Bool`-`CoShape` records only branch-vs-leaf, conflating the two atoms, so `toShape`
is not injective — a faithful embedding needs a leaf-labelled `CoShape`, a further step. -/

/-- The anamorphism: unfold an `F`-coalgebra `c` from seed `x` into a `CoShape` by walking
    the path through the seed's children. -/
def ana {X : Type} (c : X → Bool × X × X) (x : X) : List Bool → Bool
  | []           => (c x).1
  | (true :: p)  => ana c (c x).2.1 p
  | (false :: p) => ana c (c x).2.2 p

/-- `ana` commutes with the root-shape projection **by definition** (`rfl`). -/
theorem ana_isBranch {X : Type} (c : X → Bool × X × X) (x : X) :
    coIsBranch (ana c x) = (c x).1 := rfl

/-- `ana` commutes with the left-subtree projection **by definition** (`rfl`, pointwise): the
    left subtree of the unfold is the unfold of the left seed. -/
theorem ana_coLeft {X : Type} (c : X → Bool × X × X) (x : X) (p : List Bool) :
    coLeft (ana c x) p = ana c (c x).2.1 p := rfl

/-- `ana` commutes with the right-subtree projection **by definition** (`rfl`, pointwise). -/
theorem ana_coRight {X : Type} (c : X → Bool × X × X) (x : X) (p : List Bool) :
    coRight (ana c x) p = ana c (c x).2.2 p := rfl

/-- The always-branch coalgebra on `Unit`: a single state that branches into itself forever. -/
def fullCoalg : Unit → Bool × Unit × Unit := fun _ => (true, (), ())

/-- ★★ **The infinite inhabitant is an anamorphism.**  `allBranch` is the unfold of the
    always-branch coalgebra (`allBranch p = ana fullCoalg () p`): a named leaf-free
    self-pointing, presented as a coalgebra unfold. -/
theorem allBranch_eq_ana (p : List Bool) : allBranch p = ana fullCoalg () p := by
  induction p with
  | nil => rfl
  | cons b p ih => cases b <;> exact ih

/-- The finite tree's natural `F`-coalgebra: an atom is a leaf (children itself), a slash is
    a branch with its two children. -/
def treeCoalg : Tree → Bool × Tree × Tree
  | Tree.a         => (false, Tree.a, Tree.a)
  | Tree.b         => (false, Tree.b, Tree.b)
  | Tree.slash x y => (true, x, y)

/-- ★★ **The finite embedding is an anamorphism.**  `toShape = ana treeCoalg` (pointwise):
    the finite-Raw shape is the unfold of the tree's own coalgebra — the well-founded
    companion of `allBranch`'s non-well-founded unfold. -/
theorem toShape_eq_ana : ∀ (t : Tree) (p : List Bool), toShape t p = ana treeCoalg t p
  | _,              []           => by cases ‹Tree› <;> rfl
  | Tree.a,         (b :: p)     => by cases b <;> exact toShape_eq_ana Tree.a p
  | Tree.b,         (b :: p)     => by cases b <;> exact toShape_eq_ana Tree.b p
  | Tree.slash x y, (true :: p)  => toShape_eq_ana x p
  | Tree.slash x y, (false :: p) => toShape_eq_ana y p

/-- ★★ **Every coalgebra unfolds, both faces are unfolds, and the escape is an unfold gap.**
    Three facts (the third re-exported from §4):

    1. **unfold existence** — every `F`-coalgebra `c` admits an unfold `ana c` commuting with
       the `coOut` projections (`ana_isBranch`/`ana_coLeft`/`ana_coRight`, all `rfl`);
    2. **both faces are unfolds** — the finite embedding is `ana treeCoalg` (`toShape_eq_ana`)
       and the infinite inhabitant is `ana fullCoalg` (`allBranch_eq_ana`);
    3. **the escape** — `allBranch` is reached by no finite Raw (`raw_ne_allBranch`, from §4).

    So the residue's escape is, structurally, the gap between the unfolds with a leaf path
    (`tree_has_leaf_path`) and the leaf-free unfold `allBranch` (`allBranch_no_leaf`).
    ("Well-founded vs non-well-founded" is the interpretive gloss — well-foundedness is not
    formalised here.)  Honest: only unfold *existence* (not uniqueness/finality, which needs
    coinduction); the `Bool`-`CoShape` is not the injective/well-formed cotree — both
    deferred.  Conjunct 1 is `ana_isBranch ∧ ana_coLeft ∧ ana_coRight` re-bundled. -/
theorem unfold_existence_and_escape :
    (∀ {X : Type} (c : X → Bool × X × X) (x : X) (p : List Bool),
        coIsBranch (ana c x) = (c x).1
        ∧ coLeft (ana c x) p = ana c (c x).2.1 p
        ∧ coRight (ana c x) p = ana c (c x).2.2 p)
    ∧ (∀ t p, toShape t p = ana treeCoalg t p)
    ∧ (∀ p, allBranch p = ana fullCoalg () p)
    ∧ (∀ r : Raw, toShapeRaw r ≠ allBranch) :=
  ⟨fun c x p => ⟨ana_isBranch c x, ana_coLeft c x p, ana_coRight c x p⟩,
   toShape_eq_ana, allBranch_eq_ana, raw_ne_allBranch⟩

/-! ## §6 — a leaf-labelled refinement: the embedding is *faithful*

The `Bool`-`CoShape` records only branch-vs-leaf, so it conflates the two atoms.  Recording
the leaf's atom label — `LCoShape := List Bool → Option Bool` (`none` = branch, `some b` =
leaf with atom `b`) — makes the finite embedding **faithful**: trees that agree everywhere as
labelled shapes are equal (`lToShape_faithful`, stated *pointwise* to avoid `funext`).  This
closes the faithful-embedding spec item; the leaf-free inhabitant `allBranchL = fun _ => none`
still escapes (`lToShape_ne_allBranchL`).  (Uniqueness/finality of the unfold — full νF —
still needs coinduction.) -/

/-- A leaf-labelled self-pointing tree: `none` at a branch node, `some b` at a leaf with
    atom `b`. -/
def LCoShape : Type := List Bool → Option Bool

/-- The leaf-labelled embedding: atoms carry their label, a slash is a branch with children. -/
def lToShape : Tree → LCoShape
  | Tree.a,         _            => some true
  | Tree.b,         _            => some false
  | Tree.slash _ _, []           => none
  | Tree.slash x _, (true :: p)  => lToShape x p
  | Tree.slash _ y, (false :: p) => lToShape y p

/-- ★★★ **The leaf-labelled embedding is faithful.**  If two trees agree everywhere as
    labelled shapes (`∀ p, lToShape t p = lToShape t' p`), they are equal.  Stated pointwise
    (no `funext`): the root label separates atom-a / atom-b / branch, and the branch case
    recurses into the children via the `true ::`/`false ::` paths.  So the finite Raw embeds
    *faithfully* into the (leaf-labelled) co-tree model. -/
theorem lToShape_faithful : ∀ (t t' : Tree),
    (∀ p, lToShape t p = lToShape t' p) → t = t'
  | Tree.a, Tree.a, _ => rfl
  | Tree.b, Tree.b, _ => rfl
  | Tree.a, Tree.b, h => by have := h []; exact Bool.noConfusion (Option.some.inj this)
  | Tree.b, Tree.a, h => by have := h []; exact Bool.noConfusion (Option.some.inj this)
  | Tree.a, Tree.slash _ _, h => by have := h []; exact Option.noConfusion this
  | Tree.b, Tree.slash _ _, h => by have := h []; exact Option.noConfusion this
  | Tree.slash _ _, Tree.a, h => by have := h []; exact Option.noConfusion this
  | Tree.slash _ _, Tree.b, h => by have := h []; exact Option.noConfusion this
  | Tree.slash x y, Tree.slash x' y', h => by
      have hx : x = x' := lToShape_faithful x x' (fun p => h (true :: p))
      have hy : y = y' := lToShape_faithful y y' (fun p => h (false :: p))
      rw [hx, hy]

/-- The leaf-free infinite inhabitant in the labelled model. -/
def allBranchL : LCoShape := fun _ => none

/-- Every finite tree has a leaf (a `some` label somewhere). -/
theorem lTree_has_leaf : ∀ t : Tree, ∃ p b, lToShape t p = some b
  | Tree.a         => ⟨[], true, rfl⟩
  | Tree.b         => ⟨[], false, rfl⟩
  | Tree.slash x _ =>
      let ⟨p, b, hp⟩ := lTree_has_leaf x
      ⟨true :: p, b, hp⟩

/-- ★★ **The leaf-free inhabitant escapes the faithful embedding too.**  No finite tree's
    labelled shape is leaf-free: `lToShape t ≠ allBranchL` (a finite tree has a leaf, where
    its label is `some _`, while `allBranchL` is `none` everywhere). -/
theorem lToShape_ne_allBranchL (t : Tree) : lToShape t ≠ allBranchL := by
  intro h
  obtain ⟨p, b, hp⟩ := lTree_has_leaf t
  have e : allBranchL p = some b := by rw [← h]; exact hp
  exact Option.noConfusion e

/-! ## §7 — finality: `CoShape` is the final coalgebra (uniqueness of the unfold)

The "blocked by coinduction" worry was over-cautious.  Presented as **path-functions**,
`CoShape := List Bool → Bool` is the M-type — the final coalgebra of the functor
`F X = Bool × X × X` (a node label and two children) — and *uniqueness* of the unfold is
provable by induction on the **finite path**, no coinduction primitive:

  * **existence** — `ana c` is a coalgebra hom (§5);
  * **uniqueness** — `ana_unique`: any `h : X → CoShape` satisfying the (pointwise) coalgebra-
    hom equations equals `ana c` (pointwise).

So `final_coalgebra` holds ∅-axiom.  The path-induction is **label-agnostic**: the same
argument makes `List Bool → L` the final coalgebra of `F_L X = L × X × X` for any label `L`,
so the leaf-labelled `LCoShape` (`L = Option Bool`, §6) — the one with the *faithful*
embedding — is final by the same proof.  Honest scope: this is finality for the
full-binary-tree functor `F X = Bool × X × X` (a node label + two children), the
**over-approximation** of the residue's leaf-or-branch slash functor
(`{a} ⊎ {b} ⊎ {x/y : x ≠ y}`); the *exact* slash-functor νF (restricting to consistent
leaf/branch shapes with anti-reflexivity) is the residual refinement, not a coinduction
obstruction. -/

/-- ★★★ **Uniqueness of the unfold.**  Any `h : X → CoShape` satisfying the coalgebra-hom
    equations (root shape `hB`, left/right subtrees `hL`/`hR`, all pointwise) equals the
    anamorphism `ana c` — pointwise, by induction on the finite path.  No coinduction
    primitive; no `funext`. -/
theorem ana_unique {X : Type} (c : X → Bool × X × X) (h : X → CoShape)
    (hB : ∀ x, h x [] = (c x).1)
    (hL : ∀ x p, h x (true :: p) = h ((c x).2.1) p)
    (hR : ∀ x p, h x (false :: p) = h ((c x).2.2) p) :
    ∀ (x : X) (p : List Bool), h x p = ana c x p := by
  intro x p
  induction p generalizing x with
  | nil => rw [hB]; rfl
  | cons b p ih =>
      cases b with
      | true  => rw [hL]; exact ih ((c x).2.1)
      | false => rw [hR]; exact ih ((c x).2.2)

/-- ★★★ **`CoShape` is the final coalgebra of `F X = Bool × X × X`.**  Existence (`ana c` is
    a coalgebra hom — `rfl`) and uniqueness (`ana_unique` — any hom equals `ana c`,
    pointwise).  ∅-axiom, by induction on finite paths — no coinduction primitive.  The
    M-type of Bool-labelled infinite binary trees, presented as path-functions; the residue's
    escape inhabitant `allBranch` lives here.  The embedding `toShape` into *this* (Bool)
    carrier is not faithful (it conflates the atoms); the faithful embedding (§6) is in the
    parallel leaf-labelled carrier `LCoShape`, which is final by the same label-agnostic
    argument.  (Honest scope: this functor is the full-binary-tree over-approximation of the
    slash functor; the exact slash-νF refinement is residual.) -/
theorem final_coalgebra {X : Type} (c : X → Bool × X × X) :
    -- existence: `ana c` is a coalgebra hom
    ((∀ x, coIsBranch (ana c x) = (c x).1)
      ∧ (∀ x p, coLeft (ana c x) p = ana c (c x).2.1 p)
      ∧ (∀ x p, coRight (ana c x) p = ana c (c x).2.2 p))
    ∧ -- uniqueness: any coalgebra hom equals `ana c`
    (∀ h : X → CoShape,
        (∀ x, h x [] = (c x).1) →
        (∀ x p, h x (true :: p) = h ((c x).2.1) p) →
        (∀ x p, h x (false :: p) = h ((c x).2.2) p) →
        ∀ x p, h x p = ana c x p) :=
  ⟨⟨fun x => ana_isBranch c x, fun x p => ana_coLeft c x p, fun x p => ana_coRight c x p⟩,
   fun h hB hL hR => ana_unique c h hB hL hR⟩

end E213.Theory.Raw.CoResidue
