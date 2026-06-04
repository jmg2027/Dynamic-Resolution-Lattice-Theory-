import E213.Lib.Math.Real213.ModularElliptic
import E213.Meta.Int213.Core

/-!
# Euler continuants `K[a₁,…,aₙ]` and their monotonicity

The **continuant** `K[a₁,…,aₙ]` is the numerator of the finite continued fraction `[a₁;a₂,…,aₙ]`,
equivalently the `(1,1)`-entry of the matrix product `∏ᵢ [[aᵢ,1],[1,0]]`.  It satisfies Euler's
recurrence `K[a₁,…,aₙ] = aₙ·K[a₁,…,aₙ₋₁] + K[a₁,…,aₙ₋₂]`.

This file isolates the continuant as a `List Nat`-recursion (the repo previously carried it only
*implicitly* inside the Stern-Brocot matrix products `mInterval`) and proves its elementary
**monotonicity** — strictly increasing in each partial quotient and under prepending a quotient.

**Why.**  By Frobenius (1913), a Markov number `m_{p/q}` equals the continuant of the continued-fraction
shape of the rational `p/q` (its Christoffel word).  The proven Aigner orderings on Markov numbers
(Fixed Numerator / Denominator / Sum, Lee–Li–Rabideau–Schiffler 2018-20; McShane via the stable norm)
reduce to **continuant inequalities** — exactly the monotonicity here.  Those orderings are *necessary
conditions* for the Markov uniqueness (Frobenius) conjecture, which in the repo is
`markovMaxUnique_iff_markovNum_injective` (`Real213/SternBrocotMarkov` §34) — confirmed open: "Frobenius'
conjecture is equivalent to stating that [the rational → Markov] map is injective."

**Scope (honest).**  This is the *combinatorial core tool* of the Aigner program, not the bridge to
Markov numbers.  The substantial unbuilt step is the **Frobenius continuant formula** `markovNum p =
K(CF-shape of slope p)` — identifying the `mInterval` matrix-product entry with the continuant of the
continued fraction of the Christoffel word.  Even with the full bridge, Aigner monotonicity is
necessary-not-sufficient for uniqueness; the cross-node kernel `OrbitRealizabilityH` is untouched.
-/

namespace E213.Lib.Math.Real213.Continuant

open E213.Lib.Math.Real213.ModularElliptic (Mat2 mul)

/-- The continuant **pair** `(K[a₁,…,aₙ], K[a₁,…,aₙ₋₁])` carried as a state, so Euler's two-term
    recurrence becomes a one-step structural recursion on the list head.  Convention: `K[] = 1`, and
    the "previous" of the empty list is `0` (the `h₋₁ = 1`, `h₋₂ = 0` continued-fraction seed). -/
def contPair : List Nat → Nat × Nat
  | [] => (1, 0)
  | a :: t =>
      let p := contPair t
      (a * p.1 + p.2, p.1)

/-- The continuant `K[a₁,…,aₙ]` — the `(1,1)`-entry of `∏ᵢ [[aᵢ,1],[1,0]]`. -/
def continuant (l : List Nat) : Nat := (contPair l).1

/-- `K[] = 1` (the empty product). -/
theorem continuant_nil : continuant [] = 1 := rfl

/-- `K[a] = a`. -/
theorem continuant_single (a : Nat) : continuant [a] = a := by
  show a * 1 + 0 = a
  rw [Nat.add_zero, Nat.mul_one]

/-- **Euler's recurrence** `K[a,b,…] = a·K[b,…] + K[…]` — holds definitionally because the carried
    "previous" component of `contPair (b :: t)` is exactly `K[t]`. -/
theorem continuant_cons2 (a b : Nat) (t : List Nat) :
    continuant (a :: b :: t) = a * continuant (b :: t) + continuant t := rfl

/-- **Positivity**: if every partial quotient is `≥ 1`, the continuant is `≥ 1`. -/
theorem one_le_continuant : ∀ (l : List Nat), (∀ a ∈ l, 1 ≤ a) → 1 ≤ continuant l
  | [], _ => Nat.le_refl 1
  | a :: t, h => by
      have ha : 1 ≤ a := h a (List.mem_cons_self a t)
      have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem a hx)
      have hk : 1 ≤ (contPair t).1 := one_le_continuant t ht
      show 1 ≤ a * (contPair t).1 + (contPair t).2
      have h1 : 1 ≤ a * (contPair t).1 := Nat.mul_le_mul ha hk
      exact Nat.le_trans h1 (Nat.le_add_right _ _)

/-- **Strict monotonicity in the head quotient**: increasing `a₁` strictly increases `K`, provided the
    tail continuant `K[a₂,…]` is positive. -/
theorem continuant_head_strict_mono (a a' : Nat) (t : List Nat)
    (haa : a < a') (hk : 1 ≤ (contPair t).1) :
    continuant (a :: t) < continuant (a' :: t) := by
  show a * (contPair t).1 + (contPair t).2 < a' * (contPair t).1 + (contPair t).2
  have hk0 : 0 < (contPair t).1 := hk
  have step1 : a * (contPair t).1 < a * (contPair t).1 + (contPair t).1 :=
    Nat.lt_add_of_pos_right hk0
  have step2 : a * (contPair t).1 + (contPair t).1 ≤ a' * (contPair t).1 := by
    have hle : (a + 1) * (contPair t).1 ≤ a' * (contPair t).1 :=
      Nat.mul_le_mul_right _ haa
    rwa [Nat.succ_mul] at hle
  exact Nat.add_lt_add_right (Nat.lt_of_lt_of_le step1 step2) _

/-- **Prepending a quotient strictly grows the continuant**: `K[b,…] < K[a,b,…]` whenever `a ≥ 1` and
    the dropped tail continuant `K[…]` is positive.  (The continued fraction lengthening monotonicity,
    `h₋₂ = K[t] > 0` is the strict gap.) -/
theorem continuant_lt_prepend (a b : Nat) (t : List Nat)
    (ha : 1 ≤ a) (ht : 1 ≤ continuant t) :
    continuant (b :: t) < continuant (a :: b :: t) := by
  rw [continuant_cons2]
  have le1 : continuant (b :: t) ≤ a * continuant (b :: t) :=
    Nat.le_mul_of_pos_left _ ha
  exact Nat.lt_of_le_of_lt le1 (Nat.lt_add_of_pos_right ht)

/-! ## The matrix presentation: `K[a₁,…,aₙ] = (∏ᵢ [[aᵢ,1],[1,0]])₁₁`

The continuant is the `(1,1)`-entry of the product of the standard continuant matrices `[[aᵢ,1],[1,0]]`
(Frobenius/Euler).  This places `continuant` inside the repo's `Mat2` algebra (`ModularElliptic.mul`,
the same `mul` carrying `genL`/`genR`/`mInterval`), the first rung of the bridge from the path-level
continued-fraction data to the Markov node entry `markovNum = (mNode).c`. -/

/-- The standard continuant matrix `[[a,1],[1,0]]`. -/
def contMat (a : Nat) : Mat2 := ⟨(a : Int), 1, 1, 0⟩

/-- The continuant-matrix product `∏ᵢ [[aᵢ,1],[1,0]]` (identity on `[]`). -/
def contMatProd : List Nat → Mat2
  | [] => ⟨1, 0, 0, 1⟩
  | a :: t => mul (contMat a) (contMatProd t)

/-- **Continuant = matrix-product entry** (joint with the `(2,1)`-entry, the carried "previous").
    `(∏[[aᵢ,1],[1,0]])` has `(1,1)`-entry `K[a₁,…,aₙ]` and `(2,1)`-entry `K[a₂,…,aₙ]`. -/
theorem contMatProd_eq : ∀ l : List Nat,
    (contMatProd l).a = ((contPair l).1 : Int) ∧ (contMatProd l).c = ((contPair l).2 : Int)
  | [] => ⟨rfl, rfl⟩
  | a :: t => by
      obtain ⟨iha, ihc⟩ := contMatProd_eq t
      refine ⟨?_, ?_⟩
      · show (a : Int) * (contMatProd t).a + 1 * (contMatProd t).c
             = ((a * (contPair t).1 + (contPair t).2 : Nat) : Int)
        rw [iha, ihc, Int.one_mul, Int.ofNat_add, Int.ofNat_mul]
      · show (1 : Int) * (contMatProd t).a + 0 * (contMatProd t).c
             = ((contPair t).1 : Int)
        rw [iha, Int.one_mul, E213.Meta.Int213.zero_mul, Int.add_zero]

/-- ★★★★ **The continuant is the `(1,1)`-entry of `∏ᵢ [[aᵢ,1],[1,0]]`.**  The Frobenius/Euler matrix
    presentation, in the repo's `Mat2` algebra — the first rung of the continuant→`markovNum` bridge. -/
theorem continuant_eq_contMatProd (l : List Nat) :
    (contMatProd l).a = ((continuant l : Nat) : Int) :=
  (contMatProd_eq l).1

end E213.Lib.Math.Real213.Continuant
