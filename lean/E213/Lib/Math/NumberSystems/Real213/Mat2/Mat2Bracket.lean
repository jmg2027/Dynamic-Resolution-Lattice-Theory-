import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order

/-!
# The Lie bracket on `Mat2` — the commutator `[A,B] = AB − BA`

`research-notes/decomposition/practice/lie_theory.md` predicts the Lie bracket as the **q=−1
antisymmetry commutator-residue** of the `Mat2` Aut-family: read the group composition as a
*difference* of its two orders (`integers.md`'s difference-Lens `L₋` applied to `AB` and `BA`),
and the bracket `[A,B] = AB − BA` falls out, antisymmetric by the same pair-swap q=−1 bit that
signs `det`, flips `homology.md`'s face-removal `(−1)^i`, and builds ℤ's `−`.  This file grounds
the three defining facts ∅-axiom, as finite `Mat2`-entry `Int213` identities:

  * **antisymmetry** `[A,B] = −[B,A]` (`bracket_antisymm`) — the q=−1 pair-swap, not an axiom;
  * **tracelessness** `tr[A,B] = 0` (`tr_bracket_zero`) — the bracket lands in `tr`'s kernel
    (`sl₂`), the algebra-side reading of `representation.md`'s `det`/`tr` split: `tr` is the
    additive `×↦+` twin (`tr(AB) = tr(BA)`) and the commutator is forced into it;
  * **Jacobi** `[[A,B],C] + [[B,C],A] + [[C,A],B] = 0` (`jacobi`) — the q=−1 graded-Leibniz
    cyclic cancellation (the `leibniz_universal_delta4` shape), each double-bracket term a
    q=−1-signed face the cyclic sum pairs off.

plus the diagonal fixed point `[A,A] = 0` (`bracket_self`, antisymmetry's `e_i∧e_i = 0`) and the
derivation/Leibniz law `[A, BC] = [A,B]·C + B·[A,C]` (`bracket_leibniz`, the "Jacobi = graded
Leibniz" tie made concrete on the associative matrix product).

All entries are computations over `Int213`; everything closes by `ring_intZ`.  A bare `0` literal
on the right (the trace and Jacobi targets) is reached by rewriting `0` as the pure `sub_self_zero`
form `q − q` and then normalising — the Lean-core `Int.zero_*` lemmas route through `propext`, so
the repo's pure `Order.sub_self_zero` is used instead.  All ∅-axiom.

What stays open (located break, per `lie_theory.md`): the tangent/infinitesimal `ε` (`T_e G`,
the resolution dial's `h→0` residue) and BCH / the matrix exponential — the finite commutator
here *equals* the bracket on matrix groups, so the prediction lands, but no separate tangent
space or `exp(X)exp(Y) = exp(X+Y+½[X,Y]+…)` is built.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Meta.Int213.Order (sub_self_zero)

/-! ## §0 — entrywise `Mat2` additive structure

`Mat2` already carries `mul`, `det`, `tr` (`HyperbolicEllipticTrace`); the bracket needs the
additive layer `+`, `−`, `neg`, and the zero matrix.  Defined entrywise (the `Int213` operations
on the four slots), in the spirit of `Mat2CayleyHamilton.charComb` which writes the matrix
combinations out entrywise rather than via an abstract scalar action. -/

/-- The zero matrix `[[0,0],[0,0]]`. -/
def zero : Mat2 := ⟨0, 0, 0, 0⟩

/-- Entrywise matrix addition. -/
def add (m n : Mat2) : Mat2 := ⟨m.a + n.a, m.b + n.b, m.c + n.c, m.d + n.d⟩

/-- Entrywise negation. -/
def neg (m : Mat2) : Mat2 := ⟨-m.a, -m.b, -m.c, -m.d⟩

/-- Entrywise subtraction `m − n`. -/
def sub (m n : Mat2) : Mat2 := ⟨m.a - n.a, m.b - n.b, m.c - n.c, m.d - n.d⟩

/-- ★★★★ **The Lie bracket (commutator) on `Mat2`:** `[A,B] = AB − BA` — `groups.md`'s composition
    read as a *difference* of its two orders.  An entrywise `Mat2` operation on the existing `mul`
    (`HyperbolicEllipticTrace.mul`) and `Int` subtraction; the honest carrier of the Lie bracket in
    the discrete setting (on matrix groups `[X,Y]_𝔤 = XY − YX` literally). -/
def bracket (A B : Mat2) : Mat2 := sub (Mat2.mul A B) (Mat2.mul B A)

/-! ## §1 — antisymmetry: the q=−1 pair-swap residue -/

/-- ★★★★ **The bracket is antisymmetric:** `[A,B] = −[B,A]`.  This is *not* posited — it falls out
    of "read composition as a difference": swapping the operands swaps the two orders `AB ↔ BA`,
    flipping the `m−n` sign.  The same q=−1 pair-swap bit that signs `det`, flips `homology.md`'s
    `cup1_antisymmetric` (`e_i∧e_j = −(e_j∧e_i)`), and builds ℤ's `−` (`integers.md`).  Proved
    generally by `ring_intZ` per entry — no new structure, the antisymmetry is the q=−1 bit acting
    on the existing `mul`. -/
theorem bracket_antisymm (A B : Mat2) : bracket A B = neg (bracket B A) := by
  rcases A with ⟨a1, b1, c1, d1⟩
  rcases B with ⟨a2, b2, c2, d2⟩
  dsimp only [bracket, sub, neg, Mat2.mul]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;> ring_intZ

/-- ★★★★ **The self-bracket vanishes:** `[A,A] = 0` — antisymmetry's diagonal fixed point, the
    bracket's `e_i∧e_i = 0` (the `homology.md` diagonal: a q=−1-antisymmetric form vanishes on the
    diagonal).  Each entry is the syntactically identical `x − x`, closed by the pure
    `sub_self_zero`. -/
theorem bracket_self (A : Mat2) : bracket A A = zero := by
  rcases A with ⟨a, b, c, d⟩
  dsimp only [bracket, sub, zero, Mat2.mul]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;> exact sub_self_zero _

/-! ## §2 — tracelessness: the bracket lands in the `sl` (traceless) sector -/

/-- ★★★★ **The commutator is traceless:** `tr[A,B] = 0`.  This is the algebra-side reading of
    `representation.md`'s `det`/`tr` split: `det` is the multiplicative `×↦·` character of the
    *group*, `tr` the additive `×↦+` character of the *algebra*, and the bracket is forced into
    `tr`'s **kernel** — `sl₂` is exactly the traceless sector.  `tr(AB) = tr(BA)` is the finite
    entry identity, so `tr[A,B] = tr(AB) − tr(BA) = 0`.  The trace is the genuinely-additive
    structure the multiplicative `det` machinery could not host, appearing here as the traceless
    residue of the commutator.  (The two off-diagonal cross terms `b₁c₂` and `c₁b₂` of `tr(AB)`
    match `tr(BA)`'s, hence cancel.) -/
theorem tr_bracket_zero (A B : Mat2) : Mat2.tr (bracket A B) = 0 := by
  rcases A with ⟨a1, b1, c1, d1⟩
  rcases B with ⟨a2, b2, c2, d2⟩
  rw [show (0 : Int) = a1 - a1 from (sub_self_zero a1).symm]
  dsimp only [bracket, sub, Mat2.tr, Mat2.mul]
  ring_intZ

/-! ## §3 — the Jacobi identity: q=−1 graded-Leibniz cyclic cancellation -/

/-- ★★★★ **The Jacobi identity:** `[[A,B],C] + [[B,C],A] + [[C,A],B] = 0`.  The q=−1 graded-Leibniz
    cyclic cancellation predicted by `lie_theory.md` — equivalent to "`ad_A = [A,·]` is a
    derivation", the same graded three-term relation as `homology.md`'s certified
    `leibniz_universal_delta4` (`δ(α⌣β) = δα⌣β ⊕ α⌣δβ`).  Each double-bracket entry is a
    q=−1-signed face of the cyclic sum; the three terms pair off and cancel — the same mechanism as
    `∂²=0` at the Leibniz pole.  A finite `Int213` identity per entry: `dsimp` to the four entry
    polynomials, rewrite the target `0` as the pure `sub_self_zero` form, and `ring_intZ` normalises
    the cyclic sum to zero. -/
theorem jacobi (A B C : Mat2) :
    add (add (bracket (bracket A B) C) (bracket (bracket B C) A)) (bracket (bracket C A) B)
      = zero := by
  rcases A with ⟨a1, b1, c1, d1⟩
  rcases B with ⟨a2, b2, c2, d2⟩
  rcases C with ⟨a3, b3, c3, d3⟩
  dsimp only [add, bracket, sub, zero, Mat2.mul]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;>
    · rw [show (0 : Int) = a1 - a1 from (sub_self_zero a1).symm]; ring_intZ

/-! ## §4 — the derivation (Leibniz) law: `ad_A = [A,·]` is a derivation -/

/-- ★★★ **The bracket is a derivation over the matrix product:** `[A, BC] = [A,B]·C + B·[A,C]`.
    The concrete "Jacobi = graded Leibniz" tie of `lie_theory.md`: `ad_A = [A,·]` is a derivation
    of the associative product — the graded three-term relation in the form `homology.md`'s
    `leibniz_universal_delta4` already classifies.  A finite entry identity, each slot by
    `ring_intZ`. -/
theorem bracket_leibniz (A B C : Mat2) :
    bracket A (Mat2.mul B C) = add (Mat2.mul (bracket A B) C) (Mat2.mul B (bracket A C)) := by
  rcases A with ⟨a1, b1, c1, d1⟩
  rcases B with ⟨a2, b2, c2, d2⟩
  rcases C with ⟨a3, b3, c3, d3⟩
  dsimp only [bracket, sub, add, Mat2.mul]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;> ring_intZ

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket
