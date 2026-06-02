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

Narrative: `theory/essays/the_residue_as_primitive.md` (the inversion: Raw = µF, νF = `SlashNu`).
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
`CoShape := List Bool → Bool` is the M-type — *a* final coalgebra of the functor
`F X = Bool × X × X` (a node label and two children) — and *uniqueness* of the unfold is
provable by induction on the **finite path**, no coinduction primitive:

  * **existence** — `ana c` is a coalgebra hom (§5);
  * **uniqueness** — `ana_unique`: any `h : X → CoShape` satisfying the (pointwise) coalgebra-
    hom equations agrees with `ana c` *pointwise* (`∀ x p, h x p = ana c x p`).

So `final_coalgebra` holds ∅-axiom — final **up to pointwise/extensional equality** of
path-functions (the `h = ana c` form would need `funext`, deliberately avoided).  The
path-induction is **label-agnostic**: the same argument makes `List Bool → L` final for
`F_L X = L × X × X` for any label `L`, so the leaf-labelled `LCoShape` (`L = Option Bool`,
§6) — the one with the *faithful* embedding — is final by the same proof.  Honest scope: this
is finality for the full-binary-tree functor `F X = Bool × X × X`, the **over-approximation**
of the residue's leaf-or-branch slash functor (`{a} ⊎ {b} ⊎ {x/y : x ≠ y}`).  The *exact*
slash-νF (restricting to consistent leaf/branch shapes with anti-reflexive children) is a
**conjectured** subtype refinement — whether the consistent subtype is itself final, and how
to state anti-reflexivity on co-data without bisimulation, is open (not claimed free here). -/

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

/-- ★★★ **`CoShape` is a final coalgebra of `F X = Bool × X × X` (up to pointwise equality).**
    Existence (`ana c` is a coalgebra hom — `rfl`) and uniqueness (`ana_unique` — any hom
    agrees with `ana c` *pointwise*; the `h = ana c` form needs `funext`, avoided).  ∅-axiom,
    by induction on finite paths — no coinduction primitive.  The
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

/-! ## §8 — anti-reflexivity is *positive* (no bisimulation)

Toward the residue's *exact* slash functor `{a} ⊎ {b} ⊎ {x/y : x ≠ y}`: the open worry was
that the **anti-reflexivity** constraint (a branch's two children are distinct) — a
disequality of two co-data subtrees — might need a bisimulation/coinductive notion of
inequality.  It does **not**.  Inequality of co-trees is **positive**: `Distinct s t := ∃ q,
s q ≠ t q` — a single differing observation path.  (Bisimulation is needed only to prove
*equality* of co-data; *inequality* is just one differing point.)  And the witnessing path is
**constructive**: from `x ≠ y` as finite trees, `treeDiffPath` builds a path where their
labelled shapes differ, by structural recursion (`DecidableEq Tree` picks the differing
child).  So a Raw-slash's two children embed as `Distinct` co-trees (`slash_children_distinct`)
— anti-reflexivity holds *positively*, ∅-axiom, no coinduction.  (What remains for the exact
slash-νF is assembling the consistent + anti-reflexive subtype and its finality; the
anti-reflexivity itself is not the obstruction.) -/

/-- Positive inequality of co-trees: they differ at some observation path. -/
def Distinct (s t : LCoShape) : Prop := ∃ q : List Bool, s q ≠ t q

/-- ★★ **Distinct finite trees differ at a constructible path.**  From `x ≠ y` (finite
    trees), build a path `q` where the labelled shapes `lToShape x`, `lToShape y` differ — by
    structural recursion, using `DecidableEq Tree` to descend into the differing child.  The
    witness is *constructed*, not obtained from `¬∀`. -/
theorem treeDiffPath : ∀ (x y : Tree), x ≠ y → ∃ q : List Bool, lToShape x q ≠ lToShape y q
  | Tree.a,         Tree.a,         h => absurd rfl h
  | Tree.b,         Tree.b,         h => absurd rfl h
  | Tree.a,         Tree.b,         _ => ⟨[], fun e => Bool.noConfusion (Option.some.inj e)⟩
  | Tree.b,         Tree.a,         _ => ⟨[], fun e => Bool.noConfusion (Option.some.inj e)⟩
  | Tree.a,         Tree.slash _ _, _ => ⟨[], fun e => Option.noConfusion e⟩
  | Tree.b,         Tree.slash _ _, _ => ⟨[], fun e => Option.noConfusion e⟩
  | Tree.slash _ _, Tree.a,         _ => ⟨[], fun e => Option.noConfusion e⟩
  | Tree.slash _ _, Tree.b,         _ => ⟨[], fun e => Option.noConfusion e⟩
  | Tree.slash x1 x2, Tree.slash y1 y2, h =>
      if hx1 : x1 = y1 then
        have hx2 : x2 ≠ y2 := fun e => h (by rw [hx1, e])
        let ⟨q, hq⟩ := treeDiffPath x2 y2 hx2
        ⟨false :: q, hq⟩
      else
        let ⟨q, hq⟩ := treeDiffPath x1 y1 hx1
        ⟨true :: q, hq⟩

/-- ★★★ **A Raw-slash's children are positively `Distinct` — anti-reflexivity, no
    bisimulation.**  For `x ≠ y`, the two child co-trees `lToShape x`, `lToShape y` differ at
    a constructible path (`treeDiffPath`).  So the slash functor's anti-reflexivity constraint
    is a *positive* condition on co-data (a differing observation), discharged ∅-axiom — the
    feared coinductive inequality is unnecessary. -/
theorem slash_children_distinct (x y : Tree) (h : x ≠ y) :
    Distinct (lToShape x) (lToShape y) :=
  treeDiffPath x y h

/-! ## §9 — the named infinite anti-reflexive inhabitant (the left-spine)

The exact slash-νF restricts to the **anti-reflexive** subtype: at each branch the two
subtrees are `Distinct`.  `AntiRefl s := ∀ p, s p = none → Distinct (left-subtree at p)
(right-subtree at p)` (anti-reflexivity stated *positively*, §8).  The canonical infinite
anti-reflexive inhabitant is the **left-spine** `a/(a/(a/…))` — the `rawTower` limit: at every
rung the left child is the leaf `a` and the right child is the rest (distinct).  `spineL`
realises it as a path-function; it is anti-reflexive (`spineL_antiRefl`) and is reached by no
finite Raw (`spineL_escapes`).  A named infinite anti-reflexive slash-co-tree, escaping the
finite, ∅-axiom. -/

/-- The left subtree of `s` at a branch path `p`. -/
def coLeftAt (s : LCoShape) (p : List Bool) : LCoShape := fun q => s (p ++ true :: q)

/-- The right subtree of `s` at a branch path `p`. -/
def coRightAt (s : LCoShape) (p : List Bool) : LCoShape := fun q => s (p ++ false :: q)

/-- **Anti-reflexivity**: at every branch (`s p = none`), the two subtrees are `Distinct`
    (positively — a differing observation; §8).  This is the slash functor's `x ≠ y`. -/
def AntiRefl (s : LCoShape) : Prop :=
  ∀ p, s p = none → Distinct (coLeftAt s p) (coRightAt s p)

/-- The infinite left-spine `a/(a/(a/…))` as a path-function: branch on the all-false spine,
    leaf `a` (`some true`) once a `true` is taken. -/
def spineL : LCoShape
  | []           => none
  | (true :: _)  => some true
  | (false :: q) => spineL q

/-- At any branch path of the spine, the two children differ at the empty continuation:
    left descends to the leaf `a` (`some true`), right continues the branch spine (`none`). -/
theorem spineL_diff_step : ∀ p, spineL p = none →
    spineL (p ++ [true]) ≠ spineL (p ++ [false])
  | [],          _  => fun e => Option.noConfusion e
  | (true :: _), hp => Option.noConfusion hp
  | (false :: p'), hp => spineL_diff_step p' hp

/-- ★★ **The left-spine is anti-reflexive.**  At every branch, the left subtree (the leaf `a`)
    and the right subtree (the rest of the spine) differ at the empty continuation. -/
theorem spineL_antiRefl : AntiRefl spineL :=
  fun p hp => ⟨[], spineL_diff_step p hp⟩

/-- The spine is `none` (a branch) all along the all-false path — it never bottoms out. -/
theorem spineL_replicate_none : ∀ k, spineL (List.replicate k false) = none
  | 0     => rfl
  | k + 1 => spineL_replicate_none k

/-- Every finite tree's right spine bottoms out at a leaf: `lToShape t` is `some _` at some
    all-false path. -/
theorem lToShape_rightspine_leaf : ∀ t : Tree, ∃ k b, lToShape t (List.replicate k false) = some b
  | Tree.a         => ⟨0, true, rfl⟩
  | Tree.b         => ⟨0, false, rfl⟩
  | Tree.slash _ y =>
      let ⟨k, b, hk⟩ := lToShape_rightspine_leaf y
      ⟨k + 1, b, hk⟩

/-- ★★★ **The left-spine escapes every finite Raw.**  `spineL ≠ lToShape t`: the spine is a
    branch (`none`) all along the all-false path (`spineL_replicate_none`), but every finite
    tree's all-false path eventually hits a leaf (`lToShape_rightspine_leaf`).  So `spineL` is
    a *named infinite anti-reflexive* slash-co-tree (`spineL_antiRefl`) reached by no finite
    Raw — the exact-slash-νF analogue of `allBranch`, now anti-reflexive. -/
theorem spineL_escapes (t : Tree) : spineL ≠ lToShape t := by
  intro h
  obtain ⟨k, b, hk⟩ := lToShape_rightspine_leaf t
  have e : spineL (List.replicate k false) = some b := by rw [h]; exact hk
  rw [spineL_replicate_none] at e
  exact Option.noConfusion e

/-! ## §10 — the finite Raw embeds *anti-reflexively* (everywhere-distinct from canonicity)

The one subtlety of the exact slash-νF: `lToShape t` is anti-reflexive only when *every*
sub-slash of `t` has distinct children.  This is exactly the **canonical** invariant: a
canonical slash `x / y` has `cmp x y = .lt` (`Tree.canonical_slash_decompose`), hence `x ≠ y`
(`cmp x x = .eq`, `Tree.cmp_self_eq`), recursively.  So every Raw `r` (canonical) embeds
**anti-reflexively** (`raw_embeds_antiRefl`): the finite residue lands in the anti-reflexive
subtype, and `spineL` is the infinite anti-reflexive inhabitant outside it. -/

/-- A canonical slash has distinct children: `cmp x y = .lt` (canonicity) rules out `x = y`
    (`cmp x x = .eq`). -/
theorem canonical_slash_children_ne {x y : Tree} (h : (Tree.slash x y).canonical = true) :
    x ≠ y := by
  obtain ⟨_, _, hlt⟩ := Tree.canonical_slash_decompose h
  intro heq
  rw [heq, Tree.cmp_self_eq] at hlt
  exact Ordering.noConfusion hlt

/-- ★★★ **A canonical tree embeds anti-reflexively.**  `AntiRefl (lToShape t)` for every
    canonical `t`: at the root branch the children are distinct (`canonical_slash_children_ne`
    ⟹ `slash_children_distinct`); at deeper branches it reduces to the (canonical) children's
    anti-reflexivity.  Atoms are leaves (no branch — vacuous).  Induction on `t`. -/
theorem lToShape_antiRefl : ∀ (t : Tree), t.canonical = true → AntiRefl (lToShape t)
  | Tree.a,         _  => fun _ hp => Option.noConfusion hp
  | Tree.b,         _  => fun _ hp => Option.noConfusion hp
  | Tree.slash x y, hc => by
      obtain ⟨hx, hy, _⟩ := Tree.canonical_slash_decompose hc
      have hne : x ≠ y := canonical_slash_children_ne hc
      intro p hp
      match p with
      | []           => exact slash_children_distinct x y hne
      | (true :: p')  => exact lToShape_antiRefl x hx p' hp
      | (false :: p') => exact lToShape_antiRefl y hy p' hp

/-- ★★★ **The finite residue embeds anti-reflexively (and faithfully).**  For every Raw `r`,
    `lToShape r.val` is anti-reflexive (`raw_embeds_antiRefl`) — its canonical tree has
    distinct children at every node — and the embedding is faithful (`lToShape_faithful`,
    §6).  So the finite residue lands in the exact slash functor's anti-reflexive subtype;
    `spineL` (`spineL_antiRefl`) is the infinite anti-reflexive inhabitant outside it
    (`spineL_escapes`).  The exact slash-νF's defining constraint is met by the finite
    embedding, ∅-axiom — no coinduction. -/
theorem raw_embeds_antiRefl (r : Raw) : AntiRefl (lToShape r.val) :=
  lToShape_antiRefl r.val r.property

/-! ## §11 — the exact slash-νF carrier: `{Consistent ∧ AntiRefl}` co-trees

The residue's exact slash functor `{a} ⊎ {b} ⊎ {x/y : x ≠ y}` has two constraints on its
co-trees: **anti-reflexive** (branches have distinct children, §8–§10) and **consistent**
(below a leaf there is nothing — leaf labels absorb).  `SlashNu` bundles both into the carrier
type.  The finite residue embeds into it (consistent + anti-reflexive + faithful), and `spineL`
is the infinite inhabitant escaping the finite. -/

/-- **Consistency**: a leaf absorbs — below a `some b` node the label repeats. -/
def Consistent (s : LCoShape) : Prop :=
  ∀ p b, s p = some b → ∀ d, s (p ++ [d]) = some b

/-- Every finite tree's labelled shape is consistent (leaves absorb), by induction. -/
theorem lToShape_consistent : ∀ (t : Tree), Consistent (lToShape t)
  | Tree.a         => fun _ _ hb _ => hb
  | Tree.b         => fun _ _ hb _ => hb
  | Tree.slash x y => fun p b hb d => by
      match p with
      | []           => exact Option.noConfusion hb
      | (true :: p')  => exact lToShape_consistent x p' b hb d
      | (false :: p') => exact lToShape_consistent y p' b hb d

/-- The left-spine is consistent (its leaf-`a`s absorb). -/
theorem spineL_consistent : Consistent spineL
  | [],           _, hb, _ => Option.noConfusion hb
  | (true :: _),  _, hb, _ => hb
  | (false :: q), b, hb, d => spineL_consistent q b hb d

/-- The **exact slash-νF carrier**: consistent + anti-reflexive co-trees. -/
def SlashNu : Type := { s : LCoShape // Consistent s ∧ AntiRefl s }

/-- The finite residue as an exact slash-co-tree (consistent + anti-reflexive). -/
def rawToSlashNu (r : Raw) : SlashNu :=
  ⟨lToShape r.val, lToShape_consistent r.val, raw_embeds_antiRefl r⟩

/-- The infinite left-spine as an exact slash-co-tree. -/
def spineSlashNu : SlashNu := ⟨spineL, spineL_consistent, spineL_antiRefl⟩

/-- ★★ **The embedding into `SlashNu` is faithful.**  Distinct Raws give distinct exact
    slash-co-trees (pointwise): `lToShape_faithful` lifted to the subtype carrier. -/
theorem rawToSlashNu_faithful (r r' : Raw)
    (h : ∀ p, (rawToSlashNu r).val p = (rawToSlashNu r').val p) : r = r' :=
  Subtype.ext (lToShape_faithful r.val r'.val h)

/-- ★★★ **The exact slash-νF carrier, assembled.**  `SlashNu` (consistent + anti-reflexive
    co-trees) contains the finite residue *faithfully* (`rawToSlashNu`, `rawToSlashNu_faithful`)
    and the infinite anti-reflexive inhabitant `spineSlashNu` (= the left-spine), which is
    reached by no finite Raw (`spineL_escapes`).  The exact slash functor's νF carrier is
    *assembled* ∅-axiom (the type + faithful embedding + escape), no coinduction.  Whether
    `SlashNu` is the *final* coalgebra — its own finality (`ana` into `SlashNu` + uniqueness) —
    is the deepest residual (which would confirm the carrier is exactly νF); the
    over-approximation's finality is `final_coalgebra`. -/
theorem slashNu_carrier :
    (∀ r r' : Raw, (∀ p, (rawToSlashNu r).val p = (rawToSlashNu r').val p) → r = r')
    ∧ (Consistent spineSlashNu.val ∧ AntiRefl spineSlashNu.val)
    ∧ (∀ r : Raw, (rawToSlashNu r).val ≠ spineSlashNu.val) :=
  ⟨rawToSlashNu_faithful,
   ⟨spineL_consistent, spineL_antiRefl⟩,
   fun r => fun h => spineL_escapes r.val h.symm⟩

/-! ## §12 — `SlashNu` is the final slash-coalgebra (its own finality)

The slash functor's coalgebra on a seed `X` is `c : X → Option Bool × X × X`: `(c x).1 =
some b` is a **leaf** (atom `b`, children ignored), `(c x).1 = none` is a **branch** (children
seeds `(c x).2.1`, `(c x).2.2`).  The leaf-absorbing anamorphism `lAna` unfolds it into
`LCoShape`, *repeating the leaf label below a leaf* (so the unfold is `Consistent` by
construction).  `lAna` is the unique coalgebra hom (`lAna_unique`), it is always consistent
(`lAna_consistent`), and it is anti-reflexive when the coalgebra is — i.e. when each branch's
two child-seeds unfold to `Distinct` co-trees (`lAna_antiRefl`).  So `SlashNu` is the final
coalgebra of the slash functor — confirming the §11 carrier is *exactly* νF — ∅-axiom, no
coinduction. -/

/-- The leaf-absorbing anamorphism of a slash-coalgebra: branch ⇒ recurse, leaf ⇒ repeat
    the label (consistency by construction). -/
def lAna {X : Type} (c : X → Option Bool × X × X) (x : X) : List Bool → Option Bool
  | []           => (c x).1
  | (true :: p)  => match (c x).1 with
      | none   => lAna c (c x).2.1 p
      | some b => some b
  | (false :: p) => match (c x).1 with
      | none   => lAna c (c x).2.2 p
      | some b => some b

/-- `lAna` branch/leaf reductions (propext-free: `show` the defining match, then `rw` the
    head). -/
theorem lAna_true_none {X : Type} (c : X → Option Bool × X × X) (x : X) (p : List Bool)
    (h : (c x).1 = none) : lAna c x (true :: p) = lAna c (c x).2.1 p := by
  show (match (c x).1 with | none => lAna c (c x).2.1 p | some b => some b) = lAna c (c x).2.1 p
  rw [h]

theorem lAna_true_some {X : Type} (c : X → Option Bool × X × X) (x : X) (p : List Bool)
    {b : Bool} (h : (c x).1 = some b) : lAna c x (true :: p) = some b := by
  show (match (c x).1 with | none => lAna c (c x).2.1 p | some b => some b) = some b
  rw [h]

theorem lAna_false_none {X : Type} (c : X → Option Bool × X × X) (x : X) (p : List Bool)
    (h : (c x).1 = none) : lAna c x (false :: p) = lAna c (c x).2.2 p := by
  show (match (c x).1 with | none => lAna c (c x).2.2 p | some b => some b) = lAna c (c x).2.2 p
  rw [h]

theorem lAna_false_some {X : Type} (c : X → Option Bool × X × X) (x : X) (p : List Bool)
    {b : Bool} (h : (c x).1 = some b) : lAna c x (false :: p) = some b := by
  show (match (c x).1 with | none => lAna c (c x).2.2 p | some b => some b) = some b
  rw [h]

/-- ★★ **`lAna` is the unique slash-coalgebra hom.**  Any `h : X → LCoShape` satisfying the
    slash-coalgebra hom equations (root `hB`; branch `hLn`/`hRn`; leaf `hLs`/`hRs` — split by
    leaf/branch, no `match`) equals `lAna c` (pointwise, by induction on the finite path). -/
theorem lAna_unique {X : Type} (c : X → Option Bool × X × X) (h : X → LCoShape)
    (hB : ∀ x, h x [] = (c x).1)
    (hLn : ∀ x p, (c x).1 = none → h x (true :: p) = h (c x).2.1 p)
    (hLs : ∀ x p b, (c x).1 = some b → h x (true :: p) = some b)
    (hRn : ∀ x p, (c x).1 = none → h x (false :: p) = h (c x).2.2 p)
    (hRs : ∀ x p b, (c x).1 = some b → h x (false :: p) = some b) :
    ∀ (x : X) (p : List Bool), h x p = lAna c x p := by
  intro x p
  induction p generalizing x with
  | nil => exact hB x
  | cons d p ih =>
      cases d with
      | true  =>
          cases hc : (c x).1 with
          | none   => rw [hLn x p hc, lAna_true_none c x p hc]; exact ih ((c x).2.1)
          | some b => rw [hLs x p b hc, lAna_true_some c x p hc]
      | false =>
          cases hc : (c x).1 with
          | none   => rw [hRn x p hc, lAna_false_none c x p hc]; exact ih ((c x).2.2)
          | some b => rw [hRs x p b hc, lAna_false_some c x p hc]

/-- ★★ **`lAna` is always consistent.**  Below a leaf the label repeats — by construction. -/
theorem lAna_consistent {X : Type} (c : X → Option Bool × X × X) (x : X) :
    Consistent (lAna c x) := by
  intro p
  induction p generalizing x with
  | nil =>
      intro b hb d
      have hc : (c x).1 = some b := hb
      cases d with
      | true  => exact lAna_true_some c x [] hc
      | false => exact lAna_false_some c x [] hc
  | cons d p ih =>
      intro b hb e
      cases d with
      | true =>
          cases hc : (c x).1 with
          | some b' =>
              rw [lAna_true_some c x p hc] at hb
              show lAna c x (true :: (p ++ [e])) = some b
              rw [lAna_true_some c x (p ++ [e]) hc]; exact hb
          | none =>
              have hb' : lAna c (c x).2.1 p = some b := by
                rw [lAna_true_none c x p hc] at hb; exact hb
              show lAna c x (true :: (p ++ [e])) = some b
              rw [lAna_true_none c x (p ++ [e]) hc]; exact ih ((c x).2.1) b hb' e
      | false =>
          cases hc : (c x).1 with
          | some b' =>
              rw [lAna_false_some c x p hc] at hb
              show lAna c x (false :: (p ++ [e])) = some b
              rw [lAna_false_some c x (p ++ [e]) hc]; exact hb
          | none =>
              have hb' : lAna c (c x).2.2 p = some b := by
                rw [lAna_false_none c x p hc] at hb; exact hb
              show lAna c x (false :: (p ++ [e])) = some b
              rw [lAna_false_none c x (p ++ [e]) hc]; exact ih ((c x).2.2) b hb' e

/-- ★★★ **`lAna` is anti-reflexive when the coalgebra is.**  If at each branch the two
    child-seeds unfold to `Distinct` co-trees (`hAR`), then `lAna c x` is anti-reflexive. -/
theorem lAna_antiRefl {X : Type} (c : X → Option Bool × X × X)
    (hAR : ∀ y, (c y).1 = none → Distinct (lAna c (c y).2.1) (lAna c (c y).2.2)) :
    ∀ (x : X), AntiRefl (lAna c x) := by
  intro x p
  induction p generalizing x with
  | nil =>
      intro hp
      have hc : (c x).1 = none := hp
      obtain ⟨q, hq⟩ := hAR x hc
      refine ⟨q, ?_⟩
      show lAna c x (true :: q) ≠ lAna c x (false :: q)
      rw [lAna_true_none c x q hc, lAna_false_none c x q hc]; exact hq
  | cons d p ih =>
      intro hp
      cases d with
      | true =>
          cases hc : (c x).1 with
          | some b => rw [lAna_true_some c x p hc] at hp; exact Option.noConfusion hp
          | none =>
              have hp' : lAna c (c x).2.1 p = none := by
                rw [lAna_true_none c x p hc] at hp; exact hp
              obtain ⟨q, hq⟩ := ih ((c x).2.1) hp'
              refine ⟨q, ?_⟩
              show lAna c x (true :: (p ++ true :: q)) ≠ lAna c x (true :: (p ++ false :: q))
              rw [lAna_true_none c x (p ++ true :: q) hc, lAna_true_none c x (p ++ false :: q) hc]
              exact hq
      | false =>
          cases hc : (c x).1 with
          | some b => rw [lAna_false_some c x p hc] at hp; exact Option.noConfusion hp
          | none =>
              have hp' : lAna c (c x).2.2 p = none := by
                rw [lAna_false_none c x p hc] at hp; exact hp
              obtain ⟨q, hq⟩ := ih ((c x).2.2) hp'
              refine ⟨q, ?_⟩
              show lAna c x (false :: (p ++ true :: q)) ≠ lAna c x (false :: (p ++ false :: q))
              rw [lAna_false_none c x (p ++ true :: q) hc, lAna_false_none c x (p ++ false :: q) hc]
              exact hq

/-- ★★★ **`SlashNu` is the final slash-coalgebra.**  For every slash-coalgebra `c` that is
    anti-reflexive (`hAR`: each branch's children unfold distinctly), the leaf-absorbing
    unfold `lAna c` lands in `SlashNu` (consistent by `lAna_consistent`, anti-reflexive by
    `lAna_antiRefl`), and it is the *unique* coalgebra hom (`lAna_unique`, **pointwise**: `∀ x
    p, h x p = lAna c x p`; the `h = lAna c` form needs `funext`).  So `SlashNu` is exactly the
    residue's exact slash-νF among anti-reflexive coalgebras — its own finality, ∅-axiom, no
    coinduction primitive (the finite-path induction of the M-type presentation). -/
theorem slashNu_final {X : Type} (c : X → Option Bool × X × X)
    (hAR : ∀ y, (c y).1 = none → Distinct (lAna c (c y).2.1) (lAna c (c y).2.2)) :
    (∀ x : X, Consistent (lAna c x) ∧ AntiRefl (lAna c x))
    ∧ (∀ h : X → LCoShape,
        (∀ x, h x [] = (c x).1) →
        (∀ x p, (c x).1 = none → h x (true :: p) = h (c x).2.1 p) →
        (∀ x p b, (c x).1 = some b → h x (true :: p) = some b) →
        (∀ x p, (c x).1 = none → h x (false :: p) = h (c x).2.2 p) →
        (∀ x p b, (c x).1 = some b → h x (false :: p) = some b) →
        ∀ x p, h x p = lAna c x p) :=
  ⟨fun x => ⟨lAna_consistent c x, lAna_antiRefl c hAR x⟩,
   fun h hB hLn hLs hRn hRs => lAna_unique c h hB hLn hLs hRn hRs⟩

/-! ## §13 — a spine *family*: one escaping behaviour per finite Raw

`spineL` is the one canonical escaping inhabitant of `SlashNu` (the `a`-seeded left-spine).
Here it is generalised to a **`Tree`-indexed family** `spineOf t` — the left-spine whose left
child is the finite tree `t` (so `spineL` is `spineOf` of the atom `a`, pointwise).  Each
`spineOf t` is consistent, anti-reflexive (hence in `SlashNu`), and escapes every finite Raw;
and distinct seeds give `Distinct` spines.  So the whole finite µF (`Raw`) injects into the
*escaping* νF behaviours — `SlashNu` is richly populated, not just by `spineL`. -/

/-- The left-spine seeded by a finite tree `t`: a branch on the all-false spine, the left child
    at each rung being the finite tree `t`.  (`spineL` is `spineOf Tree.a`, pointwise.) -/
def spineOf (t : Tree) : LCoShape
  | []           => none
  | (true :: q)  => lToShape t q
  | (false :: q) => spineOf t q

/-- The seeded spine is `none` (a branch) all along the all-false path — never bottoms out. -/
theorem spineOf_replicate_none (t : Tree) :
    ∀ k, spineOf t (List.replicate k false) = none
  | 0     => rfl
  | k + 1 => spineOf_replicate_none t k

/-- The seeded spine is consistent: its leaf labels (inside the seed `t`) absorb. -/
theorem spineOf_consistent (t : Tree) : Consistent (spineOf t)
  | [],           _, hb, _ => Option.noConfusion hb
  | (true :: q),  b, hb, d => lToShape_consistent t q b hb d
  | (false :: q), b, hb, d => spineOf_consistent t q b hb d

/-- ★★★ **The seeded spine is anti-reflexive** (for canonical `t`).  At the root branch the
    left child is the *finite* seed `t` (bottoms out at a leaf on the all-false path) while the
    right child is the *infinite* spine (`none` everywhere on it) — so they differ; at a
    `true`-branch it reduces to the seed's own anti-reflexivity (`lToShape_antiRefl`); at a
    `false`-branch it self-recurses.  So `spineOf t ∈ SlashNu`. -/
theorem spineOf_antiRefl (t : Tree) (ht : t.canonical = true) : AntiRefl (spineOf t) := by
  intro p
  induction p with
  | nil =>
      intro _
      obtain ⟨k, b, hk⟩ := lToShape_rightspine_leaf t
      refine ⟨List.replicate k false, ?_⟩
      show lToShape t (List.replicate k false) ≠ spineOf t (List.replicate k false)
      rw [spineOf_replicate_none t k, hk]
      exact fun e => Option.noConfusion e
  | cons head tail ih =>
      cases head with
      | true  => intro hp; exact lToShape_antiRefl t ht tail hp
      | false => intro hp; exact ih hp

/-- ★★★ **The seeded spine escapes every finite Raw.**  `spineOf t ≠ lToShape s`: the seeded
    spine is a branch (`none`) all along the all-false path (`spineOf_replicate_none`), but
    every finite tree's all-false path eventually hits a leaf (`lToShape_rightspine_leaf`).  So
    every `spineOf t` is an infinite anti-reflexive inhabitant outside the finite. -/
theorem spineOf_escapes (t s : Tree) : spineOf t ≠ lToShape s := by
  intro h
  obtain ⟨k, b, hk⟩ := lToShape_rightspine_leaf s
  have e : spineOf t (List.replicate k false) = some b := by rw [h]; exact hk
  rw [spineOf_replicate_none t k] at e
  exact Option.noConfusion e

/-- ★★★ **Distinct seeds give distinct spines.**  `t ≠ t' → Distinct (spineOf t) (spineOf t')`:
    the spines differ at `true :: q` where the seeds' labelled shapes differ (`treeDiffPath`).
    So `spineOf` injects the finite trees into the escaping νF behaviours, preserving
    distinctness — `SlashNu` contains a faithful `Tree`-indexed family of escapes. -/
theorem spineOf_distinct {t t' : Tree} (h : t ≠ t') : Distinct (spineOf t) (spineOf t') := by
  obtain ⟨q, hq⟩ := treeDiffPath t t' h
  exact ⟨true :: q, hq⟩

/-- The seeded spine as an exact slash-co-tree (`SlashNu` inhabitant), for canonical `t`. -/
def spineOfSlashNu (r : Raw) : SlashNu :=
  ⟨spineOf r.val, spineOf_consistent r.val, spineOf_antiRefl r.val r.property⟩

/-- ★★★ **`SlashNu` is richly populated: the finite µF injects into the escapes.**  Bundles the
    family: every `spineOf r.val` is consistent + anti-reflexive (in `SlashNu`), escapes every
    finite Raw, and distinct Raws give `Distinct` spines.  So the escaping νF behaviours
    correspond to at least the finite Raws — a `Distinct`-preserving `Raw`-indexed family (an
    injection preserving `Distinct`, not a cardinality claim); `spineL` is one of it. -/
theorem spine_family_populates_nu :
    (∀ r : Raw, Consistent (spineOf r.val) ∧ AntiRefl (spineOf r.val))
    ∧ (∀ (r : Raw) (s : Tree), spineOf r.val ≠ lToShape s)
    ∧ (∀ r r' : Raw, r ≠ r' → Distinct (spineOf r.val) (spineOf r'.val)) :=
  ⟨fun r => ⟨spineOf_consistent r.val, spineOf_antiRefl r.val r.property⟩,
   fun r s => spineOf_escapes r.val s,
   fun r r' h => spineOf_distinct (fun e => h (Subtype.ext e))⟩

/-! ## §14 — `coSwap`: the leaf-relabel (a↔b) involution on νF

`swap` (the only Raw automorphism, `Theory/Raw/Swap`) acts on co-trees by **flipping the leaf
labels** (`a↔b`, i.e. `Bool.not`) while keeping the branch structure.  `coSwap` realises this
on `LCoShape`.  It is an involution that preserves both `SlashNu` constraints (consistent +
anti-reflexive), so it is an automorphism of the νF carrier; it carries the canonical escape
`spineL` (the `a`-spine) to a *distinct* escape (the `b`-spine).

**Honest scope caveat**: this is the *label-level* (atomic) content of `swap` — `coSwap` agrees
with `Raw.swap` on atoms (`coSwap_atom_a/b` mirror `Raw.swap_a/b`).  The *full-tree*
intertwining `coSwap ∘ lToShape = lToShape ∘ Tree.swap` does **not** hold, because `Tree.swap`
reorders a slash's children by `cmp` to stay canonical, whereas `coSwap` is positional.  So
`coSwap` is the νF leaf-relabel, not a lift of the reordering `Tree.swap`. -/

/-- The leaf-relabel involution on co-trees: flip every leaf label (`a↔b`), keep branches. -/
def coSwap (s : LCoShape) : LCoShape := fun q => (s q).map Bool.not

/-- Pointwise unfold of `coSwap` (definitional; for rewriting). -/
theorem coSwap_apply (s : LCoShape) (q : List Bool) :
    coSwap s q = Option.map Bool.not (s q) := rfl

/-- ★★ **`coSwap` is involutive** (pointwise): flipping labels twice is the identity
    (`Bool.not_not`).  Stated `∀ q` — the `coSwap (coSwap s) = s` form would need `funext`. -/
theorem coSwap_involutive (s : LCoShape) (q : List Bool) : coSwap (coSwap s) q = s q := by
  show Option.map Bool.not (Option.map Bool.not (s q)) = s q
  cases s q with
  | none   => rfl
  | some b => show some (Bool.not (Bool.not b)) = some b; rw [Bool.not_not]

/-- `coSwap` on the leaf-`a` shape is the leaf-`b` shape — the atomic content of `Raw.swap_a`. -/
theorem coSwap_atom_a (q : List Bool) : coSwap (lToShape Tree.a) q = lToShape Tree.b q := rfl

/-- `coSwap` on the leaf-`b` shape is the leaf-`a` shape — the atomic content of `Raw.swap_b`. -/
theorem coSwap_atom_b (q : List Bool) : coSwap (lToShape Tree.b) q = lToShape Tree.a q := rfl

/-- `Option.map Bool.not` is injective (since `Bool.not` is): needed to transport `Distinct`. -/
theorem optionMapNot_inj {x y : Option Bool}
    (h : Option.map Bool.not x = Option.map Bool.not y) : x = y := by
  cases x with
  | none => cases y with
    | none   => rfl
    | some b => exact Option.noConfusion h
  | some a => cases y with
    | none   => exact Option.noConfusion h
    | some b =>
        have hab : Bool.not a = Bool.not b := Option.some.inj h
        have : a = b := by rw [← Bool.not_not a, hab, Bool.not_not]
        rw [this]

/-- ★★ **`coSwap` preserves consistency**: relabelling leaves keeps leaf-absorption. -/
theorem coSwap_consistent {s : LCoShape} (h : Consistent s) : Consistent (coSwap s) := by
  intro p b' hb' d
  rw [coSwap_apply] at hb' ⊢
  cases hsp : s p with
  | none   => rw [hsp] at hb'; exact Option.noConfusion hb'
  | some c =>
      rw [hsp] at hb'
      rw [h p c hsp d]
      exact hb'

/-- ★★★ **`coSwap` preserves anti-reflexivity.**  A branch stays a branch under relabelling
    (`coSwap s p = none ⟹ s p = none`), and the distinguishing observation transports because
    `Option.map Bool.not` is injective (`optionMapNot_inj`) — `Distinct` is preserved.  So
    `coSwap` maps `SlashNu` into `SlashNu`. -/
theorem coSwap_antiRefl {s : LCoShape} (h : AntiRefl s) : AntiRefl (coSwap s) := by
  intro p hp
  have hsp : s p = none := by
    rw [coSwap_apply] at hp
    cases hx : s p with
    | none   => rfl
    | some c => rw [hx] at hp; exact Option.noConfusion hp
  obtain ⟨q, hq⟩ := h p hsp
  refine ⟨q, ?_⟩
  show Option.map Bool.not (s (p ++ true :: q)) ≠ Option.map Bool.not (s (p ++ false :: q))
  exact fun e => hq (optionMapNot_inj e)

/-- `coSwap` as an automorphism of the νF carrier `SlashNu`. -/
def coSwapSlashNu (s : SlashNu) : SlashNu :=
  ⟨coSwap s.val, coSwap_consistent s.property.1, coSwap_antiRefl s.property.2⟩

/-- ★★ **`coSwap` moves the canonical escape.**  `Distinct spineL (coSwap spineL)`: the
    `a`-spine and its leaf-flip (the `b`-spine) differ at the first left leaf (`[true]`:
    `some true` vs `some false`).  So `coSwap` carries `spineL` to a *distinct* escaping
    inhabitant — a second canonical free-running behaviour. -/
theorem coSwap_spineL_distinct : Distinct spineL (coSwap spineL) :=
  ⟨[true], fun e => Bool.noConfusion (Option.some.inj e)⟩

/-- ★★★ **`coSwap` is a νF involution-endomorphism that moves `spineL`.**  Bundles: it preserves
    consistency and anti-reflexivity (so `SlashNu → SlashNu`), is pointwise involutive, and
    carries `spineL` to a distinct escape — the leaf-relabel (`a↔b`) automorphism of the
    residue's exact slash-νF. -/
theorem coSwap_nu_endomorphism :
    (∀ s, Consistent s → Consistent (coSwap s))
    ∧ (∀ s, AntiRefl s → AntiRefl (coSwap s))
    ∧ (∀ s q, coSwap (coSwap s) q = s q)
    ∧ Distinct spineL (coSwap spineL) :=
  ⟨fun _ h => coSwap_consistent h, fun _ h => coSwap_antiRefl h,
   coSwap_involutive, coSwap_spineL_distinct⟩

/-! ## §15 — `boolSpine`: a bit-stream family of escapes (injection `(Nat→Bool) ↪ SlashNu`)

The spine has one leaf per rung; labelling those leaves by an arbitrary bit-stream
`f : Nat → Bool` gives `boolSpine f`, an escaping `SlashNu` inhabitant for *every* `f`, with
pointwise-distinct streams giving `Distinct` spines.  This is the **∅-axiom-honest form of
"uncountably many escapes"**: an injection of the function space `Nat → Bool` into `SlashNu`
preserving distinctness — *not* a cardinality theorem (`Cardinal`/`¬Countable` would pull
choice/propext).  The injectivity antecedent is the **pointwise** difference `∃ k, f k ≠ g k`
(NOT `f ≠ g`, which would need `funext` to expose a witness index). -/

/-- The bit-stream spine: at the depth-`k` left leaf put the label `f k`; the right branch
    continues the spine on the shifted stream. -/
def boolSpine (f : Nat → Bool) : LCoShape
  | []           => none
  | (true :: _)  => some (f 0)
  | (false :: q) => boolSpine (fun n => f (n + 1)) q

/-- The bit-stream spine is `none` (a branch) all along the all-false path. -/
theorem boolSpine_replicate_none (f : Nat → Bool) :
    ∀ k, boolSpine f (List.replicate k false) = none
  | 0     => rfl
  | k + 1 => boolSpine_replicate_none (fun n => f (n + 1)) k

/-- The depth-`k` left leaf of `boolSpine f` carries the label `f k`:
    `boolSpine f (replicate k false ++ [true]) = some (f k)`. -/
theorem boolSpine_leaf (f : Nat → Bool) :
    ∀ k, boolSpine f (List.replicate k false ++ [true]) = some (f k)
  | 0     => rfl
  | k + 1 => boolSpine_leaf (fun n => f (n + 1)) k

/-- The bit-stream spine is consistent: its leaf labels absorb. -/
theorem boolSpine_consistent (f : Nat → Bool) : Consistent (boolSpine f)
  | [],           _, hb, _ => Option.noConfusion hb
  | (true :: _),  _, hb, _ => hb
  | (false :: q), b, hb, d => boolSpine_consistent (fun n => f (n + 1)) q b hb d

/-- ★★ **The bit-stream spine is anti-reflexive** (every `f`).  At each branch the left child
    is a leaf (`some (f k)`) and the right child continues the spine (`none` on its all-false
    path) — distinct; a `true`-branch is a leaf (never `none`, vacuous); a `false`-branch
    recurses on the shifted stream.  So `boolSpine f ∈ SlashNu` for every `f`. -/
theorem boolSpine_antiRefl (f : Nat → Bool) : AntiRefl (boolSpine f)
  | [],           _  => ⟨[], fun e => Option.noConfusion e⟩
  | (true :: _),  hp => Option.noConfusion hp
  | (false :: q), hp => boolSpine_antiRefl (fun n => f (n + 1)) q hp

/-- ★★ **The bit-stream spine escapes every finite Raw** (every `f`): it is `none` all along
    the all-false path, but every finite tree bottoms out there. -/
theorem boolSpine_escapes (f : Nat → Bool) (s : Tree) : boolSpine f ≠ lToShape s := by
  intro h
  obtain ⟨k, b, hk⟩ := lToShape_rightspine_leaf s
  have e : boolSpine f (List.replicate k false) = some b := by rw [h]; exact hk
  rw [boolSpine_replicate_none f k] at e
  exact Option.noConfusion e

/-- ★★★ **Pointwise-distinct streams give distinct spines.**  Given a witnessing index
    `∃ k, f k ≠ g k`, the spines differ at the depth-`k` left leaf (`replicate k false ++
    [true]`, where they carry `f k` vs `g k` — `boolSpine_leaf`).  This is injectivity of
    `boolSpine` in the ∅-axiom-faithful form: the antecedent is the *pointwise* difference (no
    `funext` to expose the index, no `Cardinal`). -/
theorem boolSpine_inj {f g : Nat → Bool} (h : ∃ k, f k ≠ g k) :
    Distinct (boolSpine f) (boolSpine g) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨List.replicate k false ++ [true], ?_⟩
  rw [boolSpine_leaf f k, boolSpine_leaf g k]
  exact fun e => hk (Option.some.inj e)

/-- The bit-stream spine as a `SlashNu` inhabitant. -/
def boolSpineSlashNu (f : Nat → Bool) : SlashNu :=
  ⟨boolSpine f, boolSpine_consistent f, boolSpine_antiRefl f⟩

/-- ★★★ **`(Nat → Bool)` injects into `SlashNu`, preserving distinctness.**  Bundles: every
    bit-stream gives a `SlashNu` inhabitant (consistent + anti-reflexive), each escapes every
    finite Raw, and pointwise-distinct streams give `Distinct` spines.  So the escaping νF
    behaviours are at least as many as the infinite bit-streams — the honest ∅-axiom form of
    "the residue's escapes are uncountable" (an injection preserving `Distinct`, not a
    cardinality claim). -/
theorem boolSpine_injects_bitstreams :
    (∀ f, Consistent (boolSpine f) ∧ AntiRefl (boolSpine f))
    ∧ (∀ f (s : Tree), boolSpine f ≠ lToShape s)
    ∧ (∀ f g, (∃ k, f k ≠ g k) → Distinct (boolSpine f) (boolSpine g)) :=
  ⟨fun f => ⟨boolSpine_consistent f, boolSpine_antiRefl f⟩,
   fun f s => boolSpine_escapes f s,
   fun _ _ h => boolSpine_inj h⟩

end E213.Theory.Raw.CoResidue
