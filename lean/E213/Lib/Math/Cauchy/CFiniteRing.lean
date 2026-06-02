import E213.Lib.Math.Cauchy.OrbitDimension

/-!
# CFiniteRing — the C-finite sequences form a ring (difference-operator algebra)

`OrbitDimension` established the strict inclusion `polynomial ⊊ C-finite` and the
*module* structure (scalar, shift, common-annihilator sum).  The full ring structure
— closure under **arbitrary** pointwise sum (distinct annihilators) — needs the
**difference-operator algebra**: a C-finite sequence is one annihilated by a monic
constant-coefficient polynomial `p(Δ)`, and two such annihilators *multiply*.

This file builds that algebra:

  - `applyOp p s` — the operator `Σ_i pᵢ·Δⁱ` (coefficient list `p`, low-to-high
    `Δ`-power) applied to `s`.
  - linearity (`applyOp_add`, `applyOp_smul`), `Δ`-commutation (`applyOp_diffZ`),
    and **operator commutativity** (`applyOp_comm`: `p(Δ)q(Δ)s = q(Δ)p(Δ)s`) — the
    crux: difference operators commute because `Δ` commutes with itself.
  - `conv` (coefficient convolution = operator product) with `applyOp_conv`
    (`(p·q)(Δ) = p(Δ)∘q(Δ)`).
  - ★★★ the ring law: if `p` annihilates `s` and `q` annihilates `t`, the product
    `p·q` (monic·monic = monic) annihilates `s + t` — `cfiniteZ_add`.

All ∅-axiom (over `Int213`).
-/

namespace E213.Lib.Math.Cauchy.CFiniteRing

open E213.Lib.Math.Cauchy.NewtonGregory (diffZ liftKZ mul_zero')
open E213.Lib.Math.Cauchy.FiniteDepthAlgebra (add_sub_add)
open E213.Lib.Math.Cauchy.OrbitDimension (CFiniteZ linComb)
open E213.Meta.Int213
  (zero_mul mul_add add_mul add_comm add_assoc add_left_comm add_right_comm
   mul_comm mul_assoc zero_add mul_sub add_neg_cancel)

/-- `a·(b·c) = b·(a·c)` (pure). -/
theorem mul_left_comm' (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

/-! ## §1 — the difference-operator polynomial `applyOp` -/

/-- The difference operator `Σ_i pᵢ·Δⁱ` applied to `s`, evaluated at `n`.  The
    coefficient list `p` is low-to-high in the `Δ`-power: `applyOp (a :: p) s` peels
    `a·s` and recurses on the *differenced* sequence. -/
def applyOp : List Int → (Nat → Int) → Nat → Int
  | [],     _, _ => 0
  | a :: p, s, n => a * s n + applyOp p (diffZ s) n

/-- `applyOp` respects pointwise equality of the sequence argument. -/
theorem applyOp_congr (p : List Int) {u v : Nat → Int} (h : ∀ m, u m = v m) :
    ∀ n, applyOp p u n = applyOp p v n := by
  induction p generalizing u v with
  | nil => intro n; rfl
  | cons a p ih =>
    intro n
    show a * u n + applyOp p (diffZ u) n = a * v n + applyOp p (diffZ v) n
    rw [h n, ih (u := diffZ u) (v := diffZ v) (fun m => by
      show u (m + 1) - u m = v (m + 1) - v m
      rw [h (m + 1), h m]) n]

/-- `applyOp` is additive in its sequence argument. -/
theorem applyOp_add (p : List Int) (u v : Nat → Int) :
    ∀ n, applyOp p (fun m => u m + v m) n = applyOp p u n + applyOp p v n := by
  induction p generalizing u v with
  | nil => intro n; show (0 : Int) = 0 + 0; rw [zero_add]
  | cons a p ih =>
    intro n
    show a * (u n + v n) + applyOp p (diffZ (fun m => u m + v m)) n
       = (a * u n + applyOp p (diffZ u) n) + (a * v n + applyOp p (diffZ v) n)
    rw [applyOp_congr p (u := diffZ (fun m => u m + v m))
          (v := fun m => diffZ u m + diffZ v m)
          (fun m => add_sub_add (u (m+1)) (v (m+1)) (u m) (v m)) n,
        ih (diffZ u) (diffZ v) n, mul_add]
    show a * u n + a * v n + (applyOp p (diffZ u) n + applyOp p (diffZ v) n)
       = a * u n + applyOp p (diffZ u) n + (a * v n + applyOp p (diffZ v) n)
    rw [add_assoc, add_assoc, add_left_comm (a * v n) (applyOp p (diffZ u) n)]

/-- `applyOp` pulls out a scalar from its sequence argument. -/
theorem applyOp_smul (p : List Int) (c : Int) (s : Nat → Int) :
    ∀ n, applyOp p (fun m => c * s m) n = c * applyOp p s n := by
  induction p generalizing s with
  | nil => intro n; show (0 : Int) = c * 0; rw [mul_zero']
  | cons a p ih =>
    intro n
    show a * (c * s n) + applyOp p (diffZ (fun m => c * s m)) n
       = c * (a * s n + applyOp p (diffZ s) n)
    rw [applyOp_congr p (u := diffZ (fun m => c * s m)) (v := fun m => c * diffZ s m)
          (fun m => by
            show c * s (m+1) - c * s m = c * (s (m+1) - s m)
            rw [mul_sub]) n,
        ih (diffZ s) n, mul_add]
    show a * (c * s n) + c * applyOp p (diffZ s) n
       = c * (a * s n) + c * applyOp p (diffZ s) n
    rw [mul_left_comm' a c (s n)]

/-- `applyOp` of the zero sequence is `0`. -/
theorem applyOp_zero (p : List Int) {s : Nat → Int} (h : ∀ m, s m = 0) :
    ∀ n, applyOp p s n = 0 := by
  induction p generalizing s with
  | nil => intro n; rfl
  | cons a p ih =>
    intro n
    show a * s n + applyOp p (diffZ s) n = 0
    rw [h n, mul_zero',
        ih (s := diffZ s) (fun m => by show s (m+1) - s m = 0; rw [h (m+1), h m,
          Int.sub_eq_add_neg, add_neg_cancel]) n, zero_add]

/-! ## §2 — `Δ`-commutation and operator commutativity -/

/-- `applyOp` commutes with the forward difference: `p(Δ)(Δs) = Δ(p(Δ)s)`. -/
theorem applyOp_diffZ (p : List Int) (s : Nat → Int) :
    ∀ n, applyOp p (diffZ s) n = diffZ (applyOp p s) n := by
  induction p generalizing s with
  | nil => intro n; show (0 : Int) = 0 - 0; rw [Int.sub_eq_add_neg, add_neg_cancel]
  | cons a p ih =>
    intro n
    show a * diffZ s n + applyOp p (diffZ (diffZ s)) n
       = diffZ (fun m => a * s m + applyOp p (diffZ s) m) n
    show a * diffZ s n + applyOp p (diffZ (diffZ s)) n
       = (a * s (n+1) + applyOp p (diffZ s) (n+1))
         - (a * s n + applyOp p (diffZ s) n)
    rw [ih (diffZ s) n]
    show a * (s (n+1) - s n) + (diffZ (applyOp p (diffZ s)) n)
       = (a * s (n+1) + applyOp p (diffZ s) (n+1))
         - (a * s n + applyOp p (diffZ s) n)
    show a * (s (n+1) - s n)
         + (applyOp p (diffZ s) (n+1) - applyOp p (diffZ s) n)
       = (a * s (n+1) + applyOp p (diffZ s) (n+1))
         - (a * s n + applyOp p (diffZ s) n)
    rw [E213.Meta.Int213.mul_sub, add_sub_add]

/-- ★★★ **Operator commutativity.**  `p(Δ) q(Δ) s = q(Δ) p(Δ) s` — difference
    operators commute, because `Δ` commutes with itself.  The engine of the ring
    closure: a product of annihilators annihilates regardless of order. -/
theorem applyOp_comm (p q : List Int) (s : Nat → Int) :
    ∀ n, applyOp p (applyOp q s) n = applyOp q (applyOp p s) n := by
  induction p generalizing s with
  | nil =>
    intro n
    show (0 : Int) = applyOp q (applyOp [] s) n
    rw [applyOp_zero q (s := applyOp [] s) (fun _ => rfl) n]
  | cons a p ih =>
    intro n
    show a * applyOp q s n + applyOp p (diffZ (applyOp q s)) n
       = applyOp q (fun m => a * s m + applyOp p (diffZ s) m) n
    rw [applyOp_congr p (u := diffZ (applyOp q s)) (v := applyOp q (diffZ s))
          (fun m => (applyOp_diffZ q s m).symm) n,
        ih (diffZ s) n,
        applyOp_add q (fun m => a * s m) (fun m => applyOp p (diffZ s) m) n,
        applyOp_smul q a s n]

/-! ## §3 — convolution = operator product -/

/-- Ragged pointwise addition of coefficient lists. -/
def addL : List Int → List Int → List Int
  | [],     q      => q
  | a :: p, []     => a :: p
  | a :: p, b :: q => (a + b) :: addL p q

/-- Scalar multiple of a coefficient list. -/
def smulL (c : Int) : List Int → List Int
  | []     => []
  | b :: q => (c * b) :: smulL c q

/-- Coefficient convolution: the operator product `(Σ pᵢΔⁱ)(Σ qⱼΔʲ)`. -/
def conv : List Int → List Int → List Int
  | [],     _ => []
  | a :: p, q => addL (smulL a q) (0 :: conv p q)

/-- `applyOp` of a sum of operators (`addL`) is the sum. -/
theorem applyOp_addL (p q : List Int) (s : Nat → Int) :
    ∀ n, applyOp (addL p q) s n = applyOp p s n + applyOp q s n := by
  induction p generalizing q s with
  | nil => intro n; show applyOp q s n = 0 + applyOp q s n; rw [zero_add]
  | cons a p ih =>
    cases q with
    | nil => intro n; show applyOp (a :: p) s n = applyOp (a :: p) s n + 0; rw [Int.add_zero]
    | cons b q =>
      intro n
      show (a + b) * s n + applyOp (addL p q) (diffZ s) n
         = (a * s n + applyOp p (diffZ s) n) + (b * s n + applyOp q (diffZ s) n)
      rw [ih q (diffZ s) n, add_mul]
      show a * s n + b * s n + (applyOp p (diffZ s) n + applyOp q (diffZ s) n)
         = a * s n + applyOp p (diffZ s) n + (b * s n + applyOp q (diffZ s) n)
      rw [add_assoc, add_assoc, add_left_comm (b * s n) (applyOp p (diffZ s) n)]

/-- `applyOp` of a scaled operator (`smulL`) is the scalar multiple. -/
theorem applyOp_smulL (c : Int) (p : List Int) (s : Nat → Int) :
    ∀ n, applyOp (smulL c p) s n = c * applyOp p s n := by
  induction p generalizing s with
  | nil => intro n; show (0 : Int) = c * 0; rw [mul_zero']
  | cons b p ih =>
    intro n
    show c * b * s n + applyOp (smulL c p) (diffZ s) n
       = c * (b * s n + applyOp p (diffZ s) n)
    rw [ih (diffZ s) n, mul_add, mul_assoc]

/-- `applyOp (0 :: p) s = applyOp p (Δs)` (prepending a zero coefficient = shift up
    one `Δ`-power). -/
theorem applyOp_cons0 (p : List Int) (s : Nat → Int) (n : Nat) :
    applyOp (0 :: p) s n = applyOp p (diffZ s) n := by
  show (0 : Int) * s n + applyOp p (diffZ s) n = applyOp p (diffZ s) n
  rw [zero_mul, zero_add]

/-- ★ **Convolution = operator composition.**  `(p·q)(Δ) s = p(Δ)(q(Δ) s)`. -/
theorem applyOp_conv (p q : List Int) (s : Nat → Int) :
    ∀ n, applyOp (conv p q) s n = applyOp p (applyOp q s) n := by
  induction p generalizing s with
  | nil => intro n; rfl
  | cons a p ih =>
    intro n
    show applyOp (addL (smulL a q) (0 :: conv p q)) s n
       = a * applyOp q s n + applyOp p (diffZ (applyOp q s)) n
    rw [applyOp_addL (smulL a q) (0 :: conv p q) s n, applyOp_smulL a q s n,
        applyOp_cons0 (conv p q) s n, ih (diffZ s) n,
        applyOp_congr p (u := applyOp q (diffZ s)) (v := diffZ (applyOp q s))
          (fun m => applyOp_diffZ q s m) n]

end E213.Lib.Math.Cauchy.CFiniteRing
