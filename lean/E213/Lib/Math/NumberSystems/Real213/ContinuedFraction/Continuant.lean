import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic
import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Tactic.List213

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

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul)

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

/-! ## Reversal symmetry `K[a₁,…,aₙ] = K[aₙ,…,a₁]` via transpose

Each continuant matrix `[[aᵢ,1],[1,0]]` is **symmetric**, so `(∏ M(aᵢ))ᵀ = ∏ M(aₙ₋ᵢ) = contMatProd
(reverse)`; transpose fixes the `(1,1)`-entry, giving the classical continuant palindrome
`K[a₁,…,aₙ] = K[aₙ,…,a₁]`.  This unlocks monotonicity in the *last* quotient (hence, with the head case,
in any position) — the technical core of the Aigner orderings. -/

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (I2)

/-- Transpose of a `Mat2`. -/
def transp (M : Mat2) : Mat2 := ⟨M.a, M.c, M.b, M.d⟩

/-! Pure (propext-free) list-reversal lemmas (core `List.reverse_cons`/`reverse_append` carry `propext`). -/

private theorem reverseAux_eq {α : Type u} : ∀ (l acc : List α), l.reverseAux acc = l.reverse ++ acc
  | [], _ => rfl
  | a :: t, acc => by
      show t.reverseAux (a :: acc) = (t.reverseAux [a]) ++ acc
      rw [reverseAux_eq t (a :: acc), reverseAux_eq t [a]]
      exact (E213.Tactic.List213.append_assoc t.reverse [a] acc).symm

private theorem reverse_cons' {α : Type u} (a : α) (t : List α) :
    (a :: t).reverse = t.reverse ++ [a] :=
  reverseAux_eq t [a]

private theorem reverse_append' {α : Type u} :
    ∀ (s t : List α), (s ++ t).reverse = t.reverse ++ s.reverse
  | [], t => by
      show t.reverse = t.reverse ++ ([] : List α)
      rw [E213.Tactic.List213.append_nil]
  | a :: s, t =>
      calc (a :: (s ++ t)).reverse
          = (s ++ t).reverse ++ [a] := reverse_cons' a (s ++ t)
        _ = (t.reverse ++ s.reverse) ++ [a] := by rw [reverse_append' s t]
        _ = t.reverse ++ (s.reverse ++ [a]) :=
              E213.Tactic.List213.append_assoc t.reverse s.reverse [a]
        _ = t.reverse ++ (a :: s).reverse := by rw [reverse_cons' a s]

/-- `Mat2` extensionality (propext-free, via `congr`). -/
theorem mat2_ext {M N : Mat2} (ha : M.a = N.a) (hb : M.b = N.b) (hc : M.c = N.c) (hd : M.d = N.d) :
    M = N := by cases M; cases N; congr 1 <;> assumption

private theorem one_zero_a (x y : Int) : 1 * x + 0 * y = x := by
  rw [Int.one_mul, E213.Meta.Int213.zero_mul, Int.add_zero]
private theorem zero_one_c (x y : Int) : 0 * x + 1 * y = y := by
  rw [E213.Meta.Int213.zero_mul, Int.one_mul, E213.Meta.Int213.zero_add]
private theorem a_one_zero (x y : Int) : x * 1 + y * 0 = x := by
  rw [E213.Meta.Int213.mul_one, Int.mul_zero, Int.add_zero]
private theorem zero_one_d (x y : Int) : x * 0 + y * 1 = y := by
  rw [Int.mul_zero, E213.Meta.Int213.mul_one, E213.Meta.Int213.zero_add]

/-- Associativity of `Mat2.mul`. -/
theorem mul_assoc' (M N P : Mat2) : mul (mul M N) P = mul M (mul N P) :=
  mat2_ext (by simp only [mul]; ring_intZ) (by simp only [mul]; ring_intZ)
           (by simp only [mul]; ring_intZ) (by simp only [mul]; ring_intZ)

/-- `I2` is a left identity. -/
theorem id_mul' (M : Mat2) : mul I2 M = M :=
  mat2_ext (one_zero_a M.a M.c) (one_zero_a M.b M.d) (zero_one_c M.a M.c) (zero_one_c M.b M.d)

/-- `I2` is a right identity. -/
theorem mul_id' (M : Mat2) : mul M I2 = M :=
  mat2_ext (a_one_zero M.a M.b) (zero_one_d M.a M.b) (a_one_zero M.c M.d) (zero_one_d M.c M.d)

/-- Transpose is an anti-homomorphism: `(M·N)ᵀ = Nᵀ·Mᵀ`. -/
theorem transp_mul (M N : Mat2) : transp (mul M N) = mul (transp N) (transp M) :=
  mat2_ext (by simp only [mul, transp]; ring_intZ) (by simp only [mul, transp]; ring_intZ)
           (by simp only [mul, transp]; ring_intZ) (by simp only [mul, transp]; ring_intZ)

/-- Each continuant matrix is symmetric: `[[a,1],[1,0]]ᵀ = [[a,1],[1,0]]`. -/
theorem transp_contMat (a : Nat) : transp (contMat a) = contMat a := rfl

/-- `contMatProd [a] = [[a,1],[1,0]]`. -/
theorem contMatProd_singleton (a : Nat) : contMatProd [a] = contMat a := mul_id' (contMat a)

/-- `contMatProd` is a monoid homomorphism over append. -/
theorem contMatProd_append (l₁ l₂ : List Nat) :
    contMatProd (l₁ ++ l₂) = mul (contMatProd l₁) (contMatProd l₂) := by
  induction l₁ with
  | nil => show contMatProd l₂ = mul I2 (contMatProd l₂); rw [id_mul']
  | cons a t ih =>
      show mul (contMat a) (contMatProd (t ++ l₂))
           = mul (mul (contMat a) (contMatProd t)) (contMatProd l₂)
      rw [ih, mul_assoc']

/-- **The transpose of `∏[[aᵢ,1],[1,0]]` is the reversed product** — the matrix form of the continuant
    palindrome. -/
theorem contMatProd_reverse (l : List Nat) : transp (contMatProd l) = contMatProd l.reverse := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [reverse_cons']
      show transp (mul (contMat a) (contMatProd t)) = contMatProd (t.reverse ++ [a])
      rw [transp_mul, ih, contMatProd_append, transp_contMat, contMatProd_singleton]

/-- ★★★★★ **Continuant reversal symmetry**: `K[a₁,…,aₙ] = K[aₙ,…,a₁]`.  The classical palindrome,
    via transpose of the symmetric continuant matrices. -/
theorem continuant_reverse (l : List Nat) : continuant l.reverse = continuant l := by
  apply Int.ofNat.inj
  calc ((continuant l.reverse : Nat) : Int)
      = (contMatProd l.reverse).a := (continuant_eq_contMatProd l.reverse).symm
    _ = (transp (contMatProd l)).a := by rw [← contMatProd_reverse]
    _ = (contMatProd l).a := rfl
    _ = ((continuant l : Nat) : Int) := continuant_eq_contMatProd l

/-- ★★★★ **Strict monotonicity in the last quotient** (via reversal + the head case): increasing the
    final partial quotient strictly increases the continuant, provided the prefix continuant is positive.
    With `continuant_head_strict_mono`, the continuant is strictly monotone in *every* position. -/
theorem continuant_last_strict_mono (l : List Nat) (a a' : Nat)
    (haa : a < a') (hk : 1 ≤ (contPair l.reverse).1) :
    continuant (l ++ [a]) < continuant (l ++ [a']) := by
  rw [← continuant_reverse (l ++ [a]), ← continuant_reverse (l ++ [a']),
      reverse_append', reverse_append']
  show continuant (a :: l.reverse) < continuant (a' :: l.reverse)
  exact continuant_head_strict_mono a a' l.reverse haa hk

/-! ## The trace identity — heart of the Cohn/Frobenius formula `markovNumber = tr/3`

Completing the entry picture: `(contMatProd l)` is `[[K[l], …],[K[tail l], …]]`, with the `(1,2)`-entry
the reversed "previous" (via transpose).  The **trace** `(1,1)+(2,2)` is then `K[l] + K[middle]` — for a
Cohn word (a product of `A = [[2,1],[1,1]] = contMatProd [1,1]` and `B = [[5,2],[2,1]] = contMatProd
[2,2]`) this trace is `3·(Markov number)`, the Frobenius continuant formula. -/

/-- The `(1,2)`-entry is the reversed continuant's "previous" `K[reverse l minus last]` (via transpose). -/
theorem contMatProd_b (l : List Nat) : (contMatProd l).b = ((contPair l.reverse).2 : Int) :=
  calc (contMatProd l).b
      = (transp (contMatProd l)).c := rfl
    _ = (contMatProd l.reverse).c := by rw [contMatProd_reverse]
    _ = ((contPair l.reverse).2 : Int) := (contMatProd_eq l.reverse).2

/-- The `(2,2)`-entry for a nonempty word: `K[reverse(tail l) minus last]` — the "middle" continuant. -/
theorem contMatProd_d_cons (a : Nat) (t : List Nat) :
    (contMatProd (a :: t)).d = ((contPair t.reverse).2 : Int) := by
  show (1 : Int) * (contMatProd t).b + 0 * (contMatProd t).d = ((contPair t.reverse).2 : Int)
  rw [Int.one_mul, E213.Meta.Int213.zero_mul, Int.add_zero, contMatProd_b]

/-- ★★★★★ **The trace identity** (Cohn/Frobenius heart): for a nonempty word, the trace of
    `∏[[aᵢ,1],[1,0]]` is `K[a₁,…,aₙ] + K[a₂,…,aₙ₋₁]` (full continuant plus the "middle" continuant).
    For a Cohn word this equals `3·(Markov number)`. -/
theorem contMatProd_trace_cons (a : Nat) (t : List Nat) :
    (contMatProd (a :: t)).a + (contMatProd (a :: t)).d
      = ((continuant (a :: t) + (contPair t.reverse).2 : Nat) : Int) := by
  rw [continuant_eq_contMatProd, contMatProd_d_cons, ← Int.ofNat_add]

/-- **Concrete Cohn check**: `tr(A) = 3·1`, `tr(B) = 3·2`, `tr(AB) = 3·5` — the Markov numbers `1, 2, 5`
    as `tr/3` of the standard Cohn words `A = [1,1]`, `B = [2,2]`, `AB = [1,1,2,2]`. -/
theorem cohn_trace_examples :
    (contMatProd [1, 1]).a + (contMatProd [1, 1]).d = 3
    ∧ (contMatProd [2, 2]).a + (contMatProd [2, 2]).d = 6
    ∧ (contMatProd ([1, 1] ++ [2, 2])).a + (contMatProd ([1, 1] ++ [2, 2])).d = 15 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant
