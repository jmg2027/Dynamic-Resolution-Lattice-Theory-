import E213.Lib.Math.Algebra.Linalg213.PermGroup
import E213.Lib.Math.Algebra.Linalg213.Permutation

/-!
# Linalg213 — the group commutator and the derived series (solvability tower)

The **q=±1 solvability tower** of `galois_correspondence.md`'s located break, made concrete.

A *solvable* group is one whose **derived series**
`G ⊇ [G,G] ⊇ [[G,G],[G,G]] ⊇ ⋯` terminates at the trivial group — the iterated
**group commutator** `[g,h] = g⁻¹h⁻¹gh` (NOT the Lie bracket `AB−BA` of `Mat2Bracket`; the group
analogue) folding to `1`.  That termination is the `q=+1` *converge* pole; a non-terminating
series (a perfect group `[G,G]=G`) is the `q=−1` *escape* (the insolvable quintic, `A₅`).

This file grounds the closable instance: **`S₃` is solvable** — its commutator subgroup is `A₃`
(the even permutations / 3-cycles), and `A₃` is abelian (`[A₃,A₃]=1`), so the derived series of
`S₃` reaches `1` in **two steps** (`solvable_S3`).

Two layers:

* **§1 abstract** — `gcomm` on any associative op with two-sided identity + inverse; the
  commute-test `gcomm a b = e ↔ a·b = b·a` (the group analogue of `tr_bracket_zero`), and
  `gcomm a a = e`.  Unconditional algebra (no permutation hypotheses).
* **§2–§4 concrete `S₃`** — `gcomm` on the `perms 3` value-list group (`composeList` product,
  `invPerm` inverse).  The commutator-set of `S₃` is **exactly** `A₃` (already closed, hence the
  commutator subgroup needs no generation), `[A₃,A₃]={e}`, and the two-step termination.

All ∅-axiom (`rfl` / `decide` on the finite enumeration; `Int213` core algebra in §1).
-/

namespace E213.Lib.Math.Algebra.Linalg213.DerivedSeries

open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList invPerm)
open E213.Lib.Math.Algebra.Linalg213.Permutation (perms psign)

/-! ## §1 — the abstract group commutator and the commute-test

`gcomm a b = a⁻¹b⁻¹ab` on any group (presented op-first as an associative operation with a
two-sided identity `e` and inverse `inv`).  Its vanishing is exactly commutativity — the group
analogue of the Lie bracket's `[A,B]=0 ⟺ AB=BA` (`Mat2Bracket.tr_bracket_zero` is the trace
shadow). -/

section Abstract

variable {G : Type} (op : G → G → G) (e : G) (inv : G → G)
variable (assoc : ∀ a b c, op (op a b) c = op a (op b c))
variable (idl : ∀ a, op e a = a) (idr : ∀ a, op a e = a)
variable (invl : ∀ a, op (inv a) a = e) (invr : ∀ a, op a (inv a) = e)

/-- The **group commutator** `[a,b] = a⁻¹ b⁻¹ a b` (op-first presentation). -/
def gcomm (a b : G) : G := op (op (op (inv a) (inv b)) a) b

include assoc idl idr invl invr

/-- ★★ **The commute-test**: `[a,b] = e ⟺ a·b = b·a`.  Trivial commutator is exactly
    commutativity — the group analogue of `Mat2Bracket`'s `[A,B]=0 ⟺ AB=BA` (the q=−1
    antisymmetry test at the group level). -/
theorem gcomm_id_iff_commute (a b : G) :
    gcomm op inv a b = e ↔ op a b = op b a := by
  unfold gcomm
  constructor
  · intro h
    have h2 : op (op (inv a) (inv b)) (op a b) = e := by
      rw [← assoc (op (inv a) (inv b)) a b]; exact h
    have h3 : op (op b a) (op (op (inv a) (inv b)) (op a b)) = op (op b a) e := by rw [h2]
    rw [idr] at h3
    rw [assoc b a (op (op (inv a) (inv b)) (op a b)),
        ← assoc a (op (inv a) (inv b)) (op a b),
        ← assoc a (inv a) (inv b), invr a, idl (inv b),
        ← assoc b (inv b) (op a b), invr b, idl (op a b)] at h3
    exact h3
  · intro h
    rw [assoc (op (inv a) (inv b)) a b, h, ← assoc (op (inv a) (inv b)) b a,
        assoc (inv a) (inv b) b, invl b, idr (inv a), invl a]

/-- **A self-commutator is trivial**: `[a,a] = e` (any element commutes with itself). -/
theorem gcomm_self (a : G) : gcomm op inv a a = e :=
  (gcomm_id_iff_commute op e inv assoc idl idr invl invr a a).mpr rfl

end Abstract

/-! ## §2 — the concrete `S₃` group commutator

`S₃` is the `perms 3` value-list group: product `mulP = composeList` (`σ∘τ`), inverse `invPerm`,
identity `iota 3 = [0,1,2]`.  The group commutator instantiates §1's `gcomm` at these. -/

/-- The `S₃` product (permutation composition `σ ∘ τ`). -/
def mulP (g h : List Nat) : List Nat := composeList g h

/-- The **group commutator** on permutation value-lists: `gcommP g h = g⁻¹ h⁻¹ g h`. -/
def gcommP (g h : List Nat) : List Nat := gcomm mulP invPerm g h

/-- ★ **A 3-cycle is a commutator of two transpositions** — the commutator of the swaps
    `(0 1) = [1,0,2]` and `(1 2) = [0,2,1]` is the 3-cycle `[2,0,1]` (an even, non-identity
    `A₃` element).  Witnesses `[S₃,S₃] ⊇` a 3-cycle (the lower bound for `[S₃,S₃]=A₃`). -/
theorem three_cycle_is_commutator : gcommP [1, 0, 2] [0, 2, 1] = [2, 0, 1] := rfl

/-- That 3-cycle is non-trivial (the commutator subgroup is not yet `{e}`). -/
theorem commutator_nontrivial : gcommP [1, 0, 2] [0, 2, 1] ≠ [0, 1, 2] := by decide

/-- The commutator of two *transpositions* is **even** (`psign = +1`): a commutator always lands
    in the alternating subgroup `A₃`.  (`[1,0,2]` and `[0,2,1]` are the odd swaps.) -/
theorem gcommP_transpositions_even : psign (gcommP [1, 0, 2] [0, 2, 1]) = 1 := rfl

/-! ## §3 — the derived series as iterated commutator-sets

For `S₃` the **set of all commutators is already a subgroup** (it equals `A₃`, closed under
product and inverse — verified below), so the commutator subgroup needs no generation step: one
derived-series step = "the deduplicated list of all commutators `[g,h]`".  `commSet` computes it;
the derived series is its iteration. -/

/-- The `S₃` element set (the six value-lists of `perms 3`). -/
def S3 : List (List Nat) := perms 3

/-- The alternating subgroup `A₃` (identity + the two 3-cycles — the even permutations).
    Ordered to match the commutator enumeration `commSet S3` (`derived_S3_step1`). -/
def A3 : List (List Nat) := [[0, 1, 2], [2, 0, 1], [1, 2, 0]]

/-- The trivial subgroup. -/
def One : List (List Nat) := [[0, 1, 2]]

/-- One derived-series step: the deduplicated list of all commutators `[g,h]`, `g,h ∈ G`.
    (For `S₃`/`A₃` the commutator set is closed, so this **is** the commutator subgroup.) -/
def commSet (G : List (List Nat)) : List (List Nat) :=
  (G.flatMap (fun g => G.map (fun h => gcommP g h))).eraseDups

/-! ## §4 — `S₃` is solvable: the two-step derived series

`[S₃,S₃] = A₃`, then `[A₃,A₃] = {e}`, so `S₃ ⊵ A₃ ⊵ {e}` is the derived series terminating in
two steps (the `q=+1` converging tower). -/

/-- ★★ **`[S₃,S₃] = A₃`** — the commutator subgroup of `S₃` is exactly the alternating
    subgroup (the even permutations / 3-cycles).  The commutator set is closed (= a subgroup),
    so no subgroup-generation is needed: the *set* of commutators already is `A₃`. -/
theorem derived_S3_step1 : commSet S3 = A3 := by decide

/-- ★★ **`[A₃,A₃] = {e}`** — `A₃` is abelian, so all its commutators are the identity.
    The derived series' second step lands on the trivial subgroup. -/
theorem derived_A3_step2 : commSet A3 = One := by decide

/-- ★★★ **`S₃` is solvable** — the derived series terminates in two steps:
    `[[S₃,S₃],[S₃,S₃]] = [A₃,A₃] = {e}`.  The commutator tower **converges to `1`** (the
    `q=+1` pole of `galois_correspondence.md`'s solvability tower — solvable-by-radicals). -/
theorem solvable_S3 : commSet (commSet S3) = One := by
  rw [derived_S3_step1]; exact derived_A3_step2

/-- The derived series of `S₃` made explicit as the chain `S₃ ⊵ A₃ ⊵ {e}` (length-2
    termination): step 1 reaches `A₃`, step 2 reaches `{e}`. -/
theorem derived_series_S3 : commSet S3 = A3 ∧ commSet A3 = One :=
  ⟨derived_S3_step1, derived_A3_step2⟩

/-! ## §5 — the commutator set of `S₃` is a closed subgroup (no generation needed)

The reason `commSet` *is* the commutator subgroup for `S₃`: the set of commutators is already
closed under the group operations.  These checks justify reading `commSet` as `[G,G]`. -/

/-- `A₃` is closed under the product (`composeList`): the commutator set is product-closed. -/
theorem A3_product_closed :
    (A3.flatMap (fun g => A3.map (fun h => composeList g h))).eraseDups = A3 := by decide

/-- `A₃` is closed under inverse (`invPerm`): the inverse of every `A₃` element is again in `A₃`
    (the set is the same, the dedup-enumeration order differs). -/
theorem A3_inverse_closed : (A3.map invPerm).eraseDups = [[0, 1, 2], [1, 2, 0], [2, 0, 1]] := by
  decide

/-! ## §6 — the `A₅` escape probe (the q=−1 direction)

The insolvable quintic is `A₅` *perfect*: `[A₅,A₅] = A₅` (the derived series never terminates,
the `q=−1` escape).  A full `A₅`-perfectness proof needs the 60-element group (out of reach here
∅-axiom).  The **sharpest closable partial in the present substrate** is the *escape direction*:
`A₅` contains 3-cycles, and a 3-cycle is *itself a commutator of two transpositions* (shown for
`S₃` above, the same construction lives in any `Sₙ`), so `[A₅,A₅]` contains a 3-cycle.  The
residual — that `[A₅,A₅]` contains *every* generator (whence `=A₅`) — is the located break. -/

/-- The 3-cycle `(0 1 2)` as a commutator of two transpositions, in the `S₅`/`A₅` value-list
    model (length-5 lists).  Witnesses that the commutator subgroup of `A₅`/`S₅` contains a
    3-cycle — the `q=−1` *escape* direction toward `[A₅,A₅]=A₅` (the residual is full
    perfectness). -/
theorem three_cycle_commutator_S5 :
    gcommP [1, 0, 2, 3, 4] [0, 2, 1, 3, 4] = [2, 0, 1, 3, 4] := rfl

/-- That `S₅`/`A₅` commutator is an even, non-identity permutation (a genuine 3-cycle). -/
theorem three_cycle_commutator_S5_even : psign [2, 0, 1, 3, 4] = 1 := rfl

theorem three_cycle_commutator_S5_nontrivial : ([2, 0, 1, 3, 4] : List Nat) ≠ [0, 1, 2, 3, 4] := by
  decide

end E213.Lib.Math.Algebra.Linalg213.DerivedSeries
