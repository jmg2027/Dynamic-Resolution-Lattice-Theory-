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

open E213.Lib.Math.Cauchy.NewtonGregory (diffZ liftKZ mul_zero' add_sub_cancel_left')
open E213.Lib.Math.Cauchy.FiniteDepthAlgebra (add_sub_add liftKZ_diffZ_comm)
open E213.Lib.Math.Cauchy.OrbitDimension (CFiniteZ linComb)
open E213.Meta.Int213
  (zero_mul mul_add add_mul add_comm add_assoc add_left_comm add_right_comm
   mul_comm mul_assoc zero_add mul_sub add_neg_cancel neg_mul)

/-- `a·(b·c) = b·(a·c)` (pure). -/
theorem mul_left_comm' (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

/-- `a + b = 0 → b = -a` (pure). -/
theorem neg_eq_of_add_eq_zero {a b : Int} (h : a + b = 0) : b = -a := by
  have hh : (-a) + (a + b) = (-a) + 0 := by rw [h]
  rwa [← add_assoc, add_comm (-a) a, add_neg_cancel, zero_add, Int.add_zero] at hh

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

/-! ## §4 — the ring law: annihilators multiply -/

/-- `s` is annihilated by the operator `p`: `p(Δ) s ≡ 0`. -/
def Annih (p : List Int) (s : Nat → Int) : Prop := ∀ n, applyOp p s n = 0

/-- The product `p·q` annihilates whatever `p` annihilates (operators commute, so
    `q` is harmless on the left). -/
theorem conv_annih_left (p q : List Int) {s : Nat → Int} (h : Annih p s) :
    Annih (conv p q) s := fun n => by
  rw [applyOp_conv p q s n, applyOp_comm p q s n]
  exact applyOp_zero q h n

/-- The product `p·q` annihilates whatever `q` annihilates. -/
theorem conv_annih_right (p q : List Int) {t : Nat → Int} (h : Annih q t) :
    Annih (conv p q) t := fun n => by
  rw [applyOp_conv p q t n]
  exact applyOp_zero p h n

/-- ★★★ **The ring law (additive heart).**  If `p` annihilates `s` and `q`
    annihilates `t`, the product operator `p·q` annihilates `s + t`.  The
    constant-coefficient annihilators *multiply* — so pointwise sums of C-finite
    sequences are again C-finite (the orbit dimensions add).  This is the engine of
    `polynomial ⊊ C-finite` being a *ring*, not just a module. -/
theorem conv_annih_add (p q : List Int) {s t : Nat → Int}
    (hs : Annih p s) (ht : Annih q t) : Annih (conv p q) (fun m => s m + t m) :=
  fun n => by
    rw [applyOp_add (conv p q) s t n, conv_annih_left p q hs n,
        conv_annih_right p q ht n, zero_add]

/-! ## §5 — bridge: a C-finite sequence has a monic operator annihilator -/

/-- Peel the lowest term of a `linComb`: `Σ_{i<k+1} cᵢ Δⁱs = c₀·s + Σ_{i<k} c_{i+1} Δⁱ(Δs)`. -/
theorem linComb_peel (c : Nat → Int) (s : Nat → Int) : ∀ k n,
    linComb c s (k+1) n
      = c 0 * s n + linComb (fun i => c (i+1)) (diffZ s) k n
  | 0,   n => by
    show linComb c s 0 n + c 0 * liftKZ 0 s n
       = c 0 * s n + linComb (fun i => c (i+1)) (diffZ s) 0 n
    show (0 : Int) + c 0 * s n = c 0 * s n + 0
    rw [zero_add, Int.add_zero]
  | k+1, n => by
    show linComb c s (k+1) n + c (k+1) * liftKZ (k+1) s n
       = c 0 * s n + (linComb (fun i => c (i+1)) (diffZ s) k n
                       + c (k+1) * liftKZ k (diffZ s) n)
    rw [linComb_peel c s k n, liftKZ_diffZ_comm s k n, add_assoc]

/-- The monic difference operator `Δᵏ − Σ_{i<k} cᵢ Δⁱ` as a coefficient list
    `[-c₀, …, -c_{k-1}, 1]` (low-to-high `Δ`-power; leading coefficient `1`). -/
def opOf (c : Nat → Int) : Nat → List Int
  | 0   => [1]
  | k+1 => (-(c 0)) :: opOf (fun i => c (i+1)) k

/-- `opOf` evaluates to the difference `Δᵏs − Σ_{i<k} cᵢ Δⁱs`. -/
theorem applyOp_opOf : ∀ (c : Nat → Int) (k : Nat) (s : Nat → Int) (n : Nat),
    applyOp (opOf c k) s n = liftKZ k s n - linComb c s k n
  | c, 0,   s, n => by
    show 1 * s n + applyOp [] (diffZ s) n = liftKZ 0 s n - linComb c s 0 n
    show 1 * s n + 0 = s n - 0
    ring_intZ
  | c, k+1, s, n => by
    show -(c 0) * s n + applyOp (opOf (fun i => c (i+1)) k) (diffZ s) n
       = liftKZ (k+1) s n - linComb c s (k+1) n
    rw [applyOp_opOf (fun i => c (i+1)) k (diffZ s) n, liftKZ_diffZ_comm s k n,
        linComb_peel c s k n]
    ring_intZ

/-- `opOf` is monic: its leading (last) coefficient is `1`, for any default. -/
theorem opOf_getLastD : ∀ (c : Nat → Int) (d : Int) (k : Nat),
    (opOf c k).getLastD d = 1
  | _, _, 0   => rfl
  | c, d, k+1 => by
    show ((-(c 0)) :: opOf (fun i => c (i+1)) k).getLastD d = 1
    rw [List.getLastD_cons]
    exact opOf_getLastD (fun i => c (i+1)) (-(c 0)) k

/-- ★ **Bridge.**  Every C-finite sequence has a *monic* constant-coefficient
    operator annihilator (`Δᵏ − lower`).  This realizes `CFiniteZ` in the operator
    algebra, so the ring law `conv_annih_add` applies: the monic annihilators of two
    C-finite sequences multiply (`conv`, leading `1·1 = 1`) to a monic annihilator of
    their sum — the orbit dimensions add. -/
theorem cfiniteZ_to_annih {s : Nat → Int} (h : CFiniteZ s) :
    ∃ p, (p.getLastD 0 = 1) ∧ Annih p s := by
  obtain ⟨k, c, hrec⟩ := h
  refine ⟨opOf c k, opOf_getLastD c 0 k, fun n => ?_⟩
  rw [applyOp_opOf c k s n, hrec n, Int.sub_eq_add_neg, add_neg_cancel]

/-! ## §6 — reverse bridge: a monic annihilator gives the orbit recurrence -/

/-- `applyOp` of a monic operator `lo ++ [1]` peels the top `Δ`-power:
    `(lo ++ [1])(Δ) s = lo(Δ) s + Δ^{|lo|} s`. -/
theorem applyOp_snoc_one : ∀ (lo : List Int) (s : Nat → Int) (n : Nat),
    applyOp (lo ++ [1]) s n = applyOp lo s n + liftKZ lo.length s n
  | [],      s, n => by
    show 1 * s n + applyOp [] (diffZ s) n = 0 + liftKZ 0 s n
    show 1 * s n + 0 = 0 + s n
    ring_intZ
  | a :: lo, s, n => by
    show a * s n + applyOp (lo ++ [1]) (diffZ s) n
       = (a * s n + applyOp lo (diffZ s) n) + liftKZ (lo.length + 1) s n
    rw [applyOp_snoc_one lo (diffZ s) n, liftKZ_diffZ_comm s lo.length n, add_assoc]

/-- `applyOp` of a coefficient list is the `linComb` reading off the list (with `0`
    default beyond its length). -/
theorem applyOp_eq_linComb : ∀ (lo : List Int) (s : Nat → Int) (n : Nat),
    applyOp lo s n = linComb (fun i => lo.getD i 0) s lo.length n
  | [],      _, _ => rfl
  | a :: lo, s, n => by
    show a * s n + applyOp lo (diffZ s) n
       = linComb (fun i => (a :: lo).getD i 0) s (lo.length + 1) n
    rw [linComb_peel (fun i => (a :: lo).getD i 0) s lo.length n,
        applyOp_eq_linComb lo (diffZ s) n]
    rfl

/-- `linComb` is negated by negating every coefficient. -/
theorem linComb_neg (c : Nat → Int) (s : Nat → Int) : ∀ k n,
    linComb (fun i => -(c i)) s k n = -(linComb c s k n)
  | 0,   _ => by show (0 : Int) = -0; rw [Int.neg_zero]
  | k+1, n => by
    show linComb (fun i => -(c i)) s k n + (-(c k)) * liftKZ k s n
       = -(linComb c s k n + c k * liftKZ k s n)
    rw [linComb_neg c s k n]
    ring_intZ

/-- ★ **Reverse bridge.**  A monic operator `lo ++ [1]` annihilating `s` *is* an
    orbit recurrence `Δ^{|lo|}s = Σ_{i<|lo|} cᵢ Δⁱs`, so `s` is C-finite.  Together
    with `cfiniteZ_to_annih` this characterizes C-finite as exactly the sequences
    with a monic constant-coefficient annihilator — the orbit-recurrence definition
    equals the standard annihilating-polynomial one. -/
theorem annih_snoc_to_cfiniteZ {lo : List Int} {s : Nat → Int}
    (h : Annih (lo ++ [1]) s) : CFiniteZ s := by
  refine ⟨lo.length, (fun i => -(lo.getD i 0)), fun n => ?_⟩
  -- from h: applyOp lo s n + Δ^{|lo|}s n = 0, i.e. Δ^{|lo|}s n = -(applyOp lo s n)
  have hz : applyOp lo s n + liftKZ lo.length s n = 0 := by
    rw [← applyOp_snoc_one lo s n]; exact h n
  rw [neg_eq_of_add_eq_zero hz, applyOp_eq_linComb lo s n,
      linComb_neg (fun i => lo.getD i 0) s lo.length n]

/-! ## §7 — conv of monic operators is monic ⟹ the full ring closure `cfiniteZ_add` -/

/-- Length of a snoc. -/
theorem length_snoc : ∀ (q : List Int) (b : Int), (q ++ [b]).length = q.length + 1
  | [],     _ => rfl
  | _ :: q, b => by
    show (q ++ [b]).length + 1 = (q.length + 1) + 1
    rw [length_snoc q b]

/-- `smulL` distributes over snoc. -/
theorem smulL_snoc (c : Int) : ∀ (q : List Int) (b : Int),
    smulL c (q ++ [b]) = smulL c q ++ [c * b]
  | [],     _ => rfl
  | a :: q, b => by
    show (c * a) :: smulL c (q ++ [b]) = (c * a) :: (smulL c q ++ [c * b])
    rw [smulL_snoc c q b]

/-- `smulL` preserves length. -/
theorem length_smulL (c : Int) : ∀ (q : List Int), (smulL c q).length = q.length
  | []     => rfl
  | _ :: q => by show (smulL c q).length + 1 = q.length + 1; rw [length_smulL c q]

/-- `addL` with `[]` on the right is identity. -/
theorem addL_nil_right : ∀ (x : List Int), addL x [] = x
  | []     => rfl
  | _ :: _ => rfl

/-- `addL` of a cons with `[0]` adds `0` to the head, keeps the tail. -/
theorem addL_zero_cons (y : Int) (ys : List Int) :
    addL (y :: ys) [0] = (y + 0) :: ys := by
  show (y + 0) :: addL ys [] = (y + 0) :: ys
  rw [addL_nil_right]

/-- When the left operand is no longer than the right, `addL` commutes with snoc on
    the right (the appended element survives). -/
theorem addL_snoc_right : ∀ (x y : List Int) (b : Int), x.length ≤ y.length →
    addL x (y ++ [b]) = addL x y ++ [b]
  | [],      _,      _, _ => rfl
  | _ :: _,  [],     _, h => absurd h (Nat.not_succ_le_zero _)
  | a :: x', c :: y', b, h => by
    show (a + c) :: addL x' (y' ++ [b]) = (a + c) :: (addL x' y' ++ [b])
    rw [addL_snoc_right x' y' b (Nat.le_of_succ_le_succ h)]

/-- When the left operand is no longer than the right, `addL` has the right length. -/
theorem length_addL_right_ge : ∀ (x y : List Int), x.length ≤ y.length →
    (addL x y).length = y.length
  | [],      _,      _ => rfl
  | _ :: _,  [],     h => absurd h (Nat.not_succ_le_zero _)
  | a :: x', c :: y', h => by
    show (addL x' y').length + 1 = y'.length + 1
    rw [length_addL_right_ge x' y' (Nat.le_of_succ_le_succ h)]

/-- ★ **`conv` of two snocs.**  The operator product of `p++[a]` and `q++[b]` is a
    snoc whose appended (leading) coefficient is `a·b` — leading coefficients
    multiply, and the lower part has length `|p|+|q|`.  (The value is stated as an
    existential `v = a·b` to absorb the `+0`/`*1` syntactic noise `addL` introduces.) -/
theorem conv_snoc : ∀ (p : List Int) (a : Int) (q : List Int) (b : Int),
    ∃ r v, conv (p ++ [a]) (q ++ [b]) = r ++ [v] ∧ v = a * b
           ∧ r.length = p.length + q.length
  | [], a, [], b => by
    refine ⟨[], a * b + 0, ?_, by rw [Int.add_zero], rfl⟩
    show addL (smulL a ([] ++ [b])) [0] = [] ++ [a * b + 0]
    show addL [a * b] [0] = [a * b + 0]
    rw [addL_zero_cons]
  | [], a, c :: q', b => by
    refine ⟨(a * c + 0) :: smulL a q', a * b, ?_, rfl, ?_⟩
    · show addL (smulL a ((c :: q') ++ [b])) [0]
         = ((a * c + 0) :: smulL a q') ++ [a * b]
      rw [smulL_snoc a (c :: q') b]
      show addL ((a * c) :: (smulL a q' ++ [a * b])) [0]
         = ((a * c + 0) :: smulL a q') ++ [a * b]
      rw [addL_zero_cons]
      rfl
    · show ((a * c + 0) :: smulL a q').length = 0 + (c :: q').length
      show (smulL a q').length + 1 = 0 + (q'.length + 1)
      rw [length_smulL a q', Nat.zero_add]
  | x :: p', a, q, b => by
    obtain ⟨r', v', he, hv, hl⟩ := conv_snoc p' a q b
    have hlen : (smulL x (q ++ [b])).length ≤ (0 :: r').length := by
      show (smulL x (q ++ [b])).length ≤ r'.length + 1
      rw [length_smulL x (q ++ [b]), length_snoc q b, hl]
      exact Nat.succ_le_succ (Nat.le_add_left q.length p'.length)
    refine ⟨addL (smulL x (q ++ [b])) (0 :: r'), v', ?_, hv, ?_⟩
    · show addL (smulL x (q ++ [b])) (0 :: conv (p' ++ [a]) (q ++ [b]))
         = addL (smulL x (q ++ [b])) (0 :: r') ++ [v']
      rw [he]
      exact addL_snoc_right (smulL x (q ++ [b])) (0 :: r') v' hlen
    · rw [length_addL_right_ge (smulL x (q ++ [b])) (0 :: r') hlen]
      show r'.length + 1 = (p'.length + 1) + q.length
      rw [hl, Nat.add_right_comm]

/-- `opOf c k` is a snoc `lower ++ [1]` with `|lower| = k` (its monic structure made
    explicit, for the reverse bridge). -/
theorem opOf_snoc : ∀ (c : Nat → Int) (k : Nat),
    ∃ lo, opOf c k = lo ++ [1] ∧ lo.length = k
  | _, 0   => ⟨[], rfl, rfl⟩
  | c, k+1 => by
    obtain ⟨lo, he, hl⟩ := opOf_snoc (fun i => c (i+1)) k
    refine ⟨(-(c 0)) :: lo, ?_, ?_⟩
    · show (-(c 0)) :: opOf (fun i => c (i+1)) k = ((-(c 0)) :: lo) ++ [1]
      rw [he]; rfl
    · show lo.length + 1 = k + 1
      rw [hl]

/-- A monic annihilator `lo ++ [v]` with `v = 1` gives C-finiteness. -/
theorem annih_snoc_unit {lo : List Int} {v : Int} {s : Nat → Int}
    (hv : v = 1) (h : Annih (lo ++ [v]) s) : CFiniteZ s := by
  subst hv; exact annih_snoc_to_cfiniteZ h

/-- Every C-finite sequence has a monic annihilator in explicit snoc form. -/
theorem cfiniteZ_annih_snoc {s : Nat → Int} (h : CFiniteZ s) :
    ∃ lo, Annih (lo ++ [1]) s := by
  obtain ⟨k, c, hrec⟩ := h
  obtain ⟨lo, he, _⟩ := opOf_snoc c k
  refine ⟨lo, fun n => ?_⟩
  rw [← he, applyOp_opOf c k s n, hrec n, Int.sub_eq_add_neg, add_neg_cancel]

/-- ★★★ **The ring closure.**  C-finite is closed under pointwise addition:
    `CFiniteZ s → CFiniteZ t → CFiniteZ (s + t)`.  The monic annihilators `pₛ`, `pₜ`
    of `s`, `t` multiply (`conv`, leading `1·1 = 1` by `conv_snoc`) to a monic
    annihilator of `s + t` (`conv_annih_add`), which is again an orbit recurrence
    (`annih_snoc_unit`).  So `polynomial ⊊ C-finite` is a genuine **ring** under
    `+` — the orbit dimensions add. -/
theorem cfiniteZ_add {s t : Nat → Int} (hs : CFiniteZ s) (ht : CFiniteZ t) :
    CFiniteZ (fun m => s m + t m) := by
  obtain ⟨loS, hAs⟩ := cfiniteZ_annih_snoc hs
  obtain ⟨loT, hAt⟩ := cfiniteZ_annih_snoc ht
  obtain ⟨r, v, hconv, hv, _⟩ := conv_snoc loS 1 loT 1
  have hAnnih : Annih (conv (loS ++ [1]) (loT ++ [1])) (fun m => s m + t m) :=
    conv_annih_add (loS ++ [1]) (loT ++ [1]) hAs hAt
  rw [hconv] at hAnnih
  have hv1 : v = 1 := by rw [hv, Int.one_mul]
  exact annih_snoc_unit hv1 hAnnih

/-- **The ring is strictly larger than its summands.**  `1 + 2ⁿ` is C-finite (a
    constant polynomial plus the geometric `2ⁿ`, via `cfiniteZ_add`), yet it is
    neither a polynomial (`twoPow_not_polyDepthZ`-style: it inherits `2ⁿ`'s
    infinite divergence depth) nor a pure geometric sequence — a concrete witness
    that `+` generates genuinely new C-finite sequences. -/
theorem cfiniteZ_one_add_twoPow :
    OrbitDimension.CFiniteZ (fun n => 1 + OrbitDimension.twoPowZ n) :=
  cfiniteZ_add
    (OrbitDimension.polyDepthZ_cfiniteZ (d := 0) (s := fun _ => (1 : Int)) (fun _ => rfl))
    OrbitDimension.cfiniteZ_twoPow

/-- **C-finite is closed under subtraction** — together with `cfiniteZ_add`,
    `cfiniteZ_zero`, `cfiniteZ_neg` (`OrbitDimension`), the C-finite sequences form
    an **abelian group** under pointwise `±` (in fact a commutative ring under `+`;
    the Hadamard product is the open frontier). -/
theorem cfiniteZ_sub {s t : Nat → Int}
    (hs : CFiniteZ s) (ht : CFiniteZ t) : CFiniteZ (fun n => s n - t n) :=
  OrbitDimension.cfiniteZ_congr (fun n => by rw [Int.sub_eq_add_neg])
    (cfiniteZ_add hs (OrbitDimension.cfiniteZ_neg ht))

/-! ## §8 — the shift `E` is a difference operator: `E = I + Δ` (toward C-D) -/

/-- ★ **The shift is a difference operator.**  `applyOp [1,1] = E`: the operator
    `I + Δ` is the forward shift, `(I+Δ)s(n) = s(n) + (s(n+1)−s(n)) = s(n+1)`.  This
    is `E = I + Δ` realized in the `Δ`-operator algebra — the bridge from the
    shift-recurrence (standard C-finite) picture to the `Δ`-orbit one. -/
theorem applyOp_shift (s : Nat → Int) (n : Nat) : applyOp [1, 1] s n = s (n + 1) := by
  show 1 * s n + (1 * diffZ s n + 0) = s (n + 1)
  rw [Int.one_mul, Int.one_mul, Int.add_zero]
  show s n + (s (n + 1) - s n) = s (n + 1)
  rw [add_sub_cancel_left']

/-- The `k`-fold shift `Eᵏ` as a `Δ`-operator: `Eᵏ = (I+Δ)ᵏ`, built by convolving
    `[1,1]` with itself `k` times. -/
def ePow : Nat → List Int
  | 0   => [1]
  | i+1 => conv [1, 1] (ePow i)

/-- ★ **`Eᵏ` as a difference operator computes the `k`-shift.**  `applyOp (ePow k) s n
    = s(n+k)` — the shift is a polynomial in `Δ` (`(I+Δ)ᵏ`).  So a monic shift
    recurrence is a monic `Δ`-operator annihilator: the foundation of C-D
    (orbit dimension = recurrence order). -/
theorem applyOp_ePow (s : Nat → Int) : ∀ i n, applyOp (ePow i) s n = s (n + i)
  | 0,   n => by
    show 1 * s n + 0 = s (n + 0)
    rw [Int.one_mul, Int.add_zero, Nat.add_zero]
  | i+1, n => by
    show applyOp (conv [1, 1] (ePow i)) s n = s (n + (i + 1))
    rw [applyOp_conv [1, 1] (ePow i) s n, applyOp_shift (applyOp (ePow i) s) n,
        applyOp_ePow s i (n + 1), Nat.add_right_comm n 1 i]
    rfl

/-! ## §9 — C-D reverse: a monic shift recurrence ⟹ C-finite -/

/-- The shift combination `Σ_{i<k} bᵢ · s(n+i)`. -/
def shiftSum (b : Nat → Int) (s : Nat → Int) : Nat → Nat → Int
  | 0,   _ => 0
  | k+1, n => shiftSum b s k n + b k * s (n + k)

/-- `s` satisfies a **monic order-`k` shift recurrence** `s(n+k) = Σ_{i<k} bᵢ s(n+i)`
    — the standard definition of a C-finite (constant-recursive) sequence. -/
def ShiftRecZ (k : Nat) (b s : Nat → Int) : Prop := ∀ n, s (n + k) = shiftSum b s k n

/-- The `Δ`-operator for a shift combination: `Σ_{i<k} bᵢ · Eⁱ = Σ_{i<k} bᵢ · ePow i`. -/
def eCombo (b : Nat → Int) : Nat → List Int
  | 0   => []
  | k+1 => addL (eCombo b k) (smulL (b k) (ePow k))

/-- `applyOp (eCombo b k) s n = Σ_{i<k} bᵢ s(n+i)` — the `Δ`-operator `eCombo` realizes
    the shift combination (since each `ePow i` realizes the `i`-shift). -/
theorem applyOp_eCombo (b : Nat → Int) (s : Nat → Int) : ∀ k n,
    applyOp (eCombo b k) s n = shiftSum b s k n
  | 0,   _ => rfl
  | k+1, n => by
    show applyOp (addL (eCombo b k) (smulL (b k) (ePow k))) s n
       = shiftSum b s k n + b k * s (n + k)
    rw [applyOp_addL (eCombo b k) (smulL (b k) (ePow k)) s n,
        applyOp_smulL (b k) (ePow k) s n, applyOp_ePow s k n, applyOp_eCombo b s k n]

/-- `ePow k` is monic of degree `k`: `ePow k = lo ++ [v]` with `v = 1`, `|lo| = k`
    (`Eᵏ = (I+Δ)ᵏ` has leading `Δ`-coefficient `1`). -/
theorem ePow_eq_snoc : ∀ k, ∃ lo v, ePow k = lo ++ [v] ∧ v = 1 ∧ lo.length = k
  | 0   => ⟨[], 1, rfl, rfl, rfl⟩
  | k+1 => by
    obtain ⟨lo, v, he, hv, hl⟩ := ePow_eq_snoc k
    obtain ⟨r, w, hc, hw, hrl⟩ := conv_snoc [1] 1 lo v
    refine ⟨r, w, ?_, ?_, ?_⟩
    · show conv [1, 1] (ePow k) = r ++ [w]
      rw [he]; exact hc
    · rw [hw, hv, Int.one_mul]
    · rw [hrl, hl]; exact Nat.add_comm 1 k

/-- `|eCombo b k| ≤ k` — the shift combination has degree `< k`, so its `Δ`-list is
    shorter than `ePow k` (which has length `k+1`). -/
theorem eCombo_length_le (b : Nat → Int) : ∀ k, (eCombo b k).length ≤ k
  | 0   => Nat.le_refl 0
  | k+1 => by
    obtain ⟨lo, v, he, _, hl⟩ := ePow_eq_snoc k
    have hsl : (smulL (b k) (ePow k)).length = k + 1 := by
      rw [length_smulL, he, length_snoc, hl]
    have hle : (eCombo b k).length ≤ (smulL (b k) (ePow k)).length := by
      rw [hsl]; exact Nat.le_succ_of_le (eCombo_length_le b k)
    have heq : (eCombo b (k+1)).length = k + 1 := by
      show (addL (eCombo b k) (smulL (b k) (ePow k))).length = k + 1
      rw [length_addL_right_ge (eCombo b k) (smulL (b k) (ePow k)) hle, hsl]
    exact Nat.le_of_eq heq

/-- ★★★ **C-D reverse direction.**  A sequence satisfying a monic order-`k` *shift*
    recurrence is C-finite (its `Δ`-orbit dimension is `≤ k`).  The shift annihilator
    `Eᵏ − Σ bᵢ Eⁱ` is the `Δ`-operator `ePow k − Σ bᵢ ePow i` (`applyOp_ePow`), which
    is monic of degree `k` (the lower `ePow i` are shorter than `ePow k`, so the
    leading `Δᵏ`-coefficient is untouched — `addL_snoc_right`).  So the standard
    constant-recursive definition implies the `Δ`-orbit-recurrence one — half of
    "orbit dimension = recurrence order". -/
theorem cfiniteZ_of_shiftRec {k : Nat} {b s : Nat → Int} (h : ShiftRecZ k b s) :
    CFiniteZ s := by
  obtain ⟨loK, vK, heK, hvK, hlK⟩ := ePow_eq_snoc k
  have hnsl : (smulL (-1) (eCombo b k)).length ≤ loK.length := by
    rw [length_smulL, hlK]; exact eCombo_length_le b k
  refine annih_snoc_unit (lo := addL (smulL (-1) (eCombo b k)) loK) (v := vK) hvK (fun n => ?_)
  rw [← addL_snoc_right (smulL (-1) (eCombo b k)) loK vK hnsl, ← heK,
      applyOp_addL (smulL (-1) (eCombo b k)) (ePow k) s n,
      applyOp_smulL (-1) (eCombo b k) s n, applyOp_eCombo b s k n, applyOp_ePow s k n, h n]
  rw [neg_mul, Int.one_mul, add_comm, add_neg_cancel]

/-- **End-to-end validation of the reverse bridge.**  Fibonacci's natural *shift*
    recurrence `f(n+2) = f(n+1) + f(n)` (order 2, coefficients `1, 1`) feeds
    `cfiniteZ_of_shiftRec` to re-derive `CFiniteZ fibZ` — independently of the
    `Δ`-recurrence route `OrbitDimension.cfiniteZ_fib`.  Both give orbit dimension 2:
    a concrete instance of "shift recurrence order = `Δ`-orbit dimension". -/
theorem cfiniteZ_fib_via_shift : CFiniteZ OrbitDimension.fibZ :=
  cfiniteZ_of_shiftRec (k := 2) (b := fun _ => 1) (fun n => by
    show OrbitDimension.fibZ (n + 2)
       = (0 + 1 * OrbitDimension.fibZ (n + 0)) + 1 * OrbitDimension.fibZ (n + 1)
    rw [zero_add, Int.one_mul, Int.one_mul]
    show OrbitDimension.fibZ (n + 1) + OrbitDimension.fibZ n
       = OrbitDimension.fibZ n + OrbitDimension.fibZ (n + 1)
    exact add_comm _ _)

/-! ## §10 — the shift-operator algebra `applyShift` (`Δ = applyShift [-1,1]`) -/

/-- The shift operator `Σ_i qᵢ·Eⁱ` applied to `s` (`E` = forward shift), evaluated at
    `n`.  Mirror of `applyOp` with `E` in place of `Δ`: `applyShift (a::q) s` peels
    `a·s` and recurses on the *shifted* sequence. -/
def applyShift : List Int → (Nat → Int) → Nat → Int
  | [],     _, _ => 0
  | a :: q, s, n => a * s n + applyShift q (fun m => s (m + 1)) n

/-- `applyShift` respects pointwise equality of the sequence argument. -/
theorem applyShift_congr (q : List Int) {u v : Nat → Int} (h : ∀ m, u m = v m) :
    ∀ n, applyShift q u n = applyShift q v n := by
  induction q generalizing u v with
  | nil => intro n; rfl
  | cons a q ih =>
    intro n
    show a * u n + applyShift q (fun m => u (m + 1)) n
       = a * v n + applyShift q (fun m => v (m + 1)) n
    rw [h n, ih (u := fun m => u (m + 1)) (v := fun m => v (m + 1)) (fun m => h (m + 1)) n]

/-- `applyShift` is additive in its sequence argument. -/
theorem applyShift_add (q : List Int) (u v : Nat → Int) :
    ∀ n, applyShift q (fun m => u m + v m) n = applyShift q u n + applyShift q v n := by
  induction q generalizing u v with
  | nil => intro n; show (0 : Int) = 0 + 0; rw [zero_add]
  | cons a q ih =>
    intro n
    show a * (u n + v n) + applyShift q (fun m => u (m + 1) + v (m + 1)) n
       = (a * u n + applyShift q (fun m => u (m + 1)) n)
         + (a * v n + applyShift q (fun m => v (m + 1)) n)
    rw [ih (fun m => u (m + 1)) (fun m => v (m + 1)) n, mul_add]
    show a * u n + a * v n + (applyShift q (fun m => u (m + 1)) n
           + applyShift q (fun m => v (m + 1)) n)
       = a * u n + applyShift q (fun m => u (m + 1)) n
         + (a * v n + applyShift q (fun m => v (m + 1)) n)
    rw [add_assoc, add_assoc, add_left_comm (a * v n) (applyShift q (fun m => u (m + 1)) n)]

/-- `applyShift` pulls out a scalar from its sequence argument. -/
theorem applyShift_smul (q : List Int) (c : Int) (s : Nat → Int) :
    ∀ n, applyShift q (fun m => c * s m) n = c * applyShift q s n := by
  induction q generalizing s with
  | nil => intro n; show (0 : Int) = c * 0; rw [mul_zero']
  | cons a q ih =>
    intro n
    show a * (c * s n) + applyShift q (fun m => c * s (m + 1)) n
       = c * (a * s n + applyShift q (fun m => s (m + 1)) n)
    rw [ih (fun m => s (m + 1)) n, mul_add]
    show a * (c * s n) + c * applyShift q (fun m => s (m + 1)) n
       = c * (a * s n) + c * applyShift q (fun m => s (m + 1)) n
    rw [mul_left_comm' a c (s n)]

/-- `applyShift` of the zero sequence is `0`. -/
theorem applyShift_zero (q : List Int) {s : Nat → Int} (h : ∀ m, s m = 0) :
    ∀ n, applyShift q s n = 0 := by
  induction q generalizing s with
  | nil => intro n; rfl
  | cons a q ih =>
    intro n
    show a * s n + applyShift q (fun m => s (m + 1)) n = 0
    rw [h n, mul_zero', ih (s := fun m => s (m + 1)) (fun m => h (m + 1)) n, zero_add]

/-- `applyShift` commutes with the shift: `applyShift q (E s) n = (applyShift q s)(n+1)`. -/
theorem applyShift_shift (q : List Int) (s : Nat → Int) : ∀ n,
    applyShift q (fun m => s (m + 1)) n = applyShift q s (n + 1) := by
  induction q generalizing s with
  | nil => intro n; rfl
  | cons a q ih =>
    intro n
    show a * s (n + 1) + applyShift q (fun m => s (m + 1 + 1)) n
       = a * s (n + 1) + applyShift q (fun m => s (m + 1)) (n + 1)
    rw [ih (fun m => s (m + 1)) n]

/-- `applyShift` of a sum of operators (`addL`) is the sum. -/
theorem applyShift_addL (p q : List Int) (s : Nat → Int) :
    ∀ n, applyShift (addL p q) s n = applyShift p s n + applyShift q s n := by
  induction p generalizing q s with
  | nil => intro n; show applyShift q s n = 0 + applyShift q s n; rw [zero_add]
  | cons a p ih =>
    cases q with
    | nil => intro n; show applyShift (a :: p) s n = applyShift (a :: p) s n + 0; rw [Int.add_zero]
    | cons b q =>
      intro n
      show (a + b) * s n + applyShift (addL p q) (fun m => s (m + 1)) n
         = (a * s n + applyShift p (fun m => s (m + 1)) n)
           + (b * s n + applyShift q (fun m => s (m + 1)) n)
      rw [ih q (fun m => s (m + 1)) n, add_mul]
      show a * s n + b * s n + (applyShift p (fun m => s (m + 1)) n
             + applyShift q (fun m => s (m + 1)) n)
         = a * s n + applyShift p (fun m => s (m + 1)) n
           + (b * s n + applyShift q (fun m => s (m + 1)) n)
      rw [add_assoc, add_assoc, add_left_comm (b * s n) (applyShift p (fun m => s (m + 1)) n)]

/-- `applyShift` of a scaled operator (`smulL`) is the scalar multiple. -/
theorem applyShift_smulL (c : Int) (p : List Int) (s : Nat → Int) :
    ∀ n, applyShift (smulL c p) s n = c * applyShift p s n := by
  induction p generalizing s with
  | nil => intro n; show (0 : Int) = c * 0; rw [mul_zero']
  | cons b p ih =>
    intro n
    show c * b * s n + applyShift (smulL c p) (fun m => s (m + 1)) n
       = c * (b * s n + applyShift p (fun m => s (m + 1)) n)
    rw [ih (fun m => s (m + 1)) n, mul_add, mul_assoc]

/-- `applyShift (0 :: p) s = applyShift p (E s)` (prepending a zero = shift up one `E`-power). -/
theorem applyShift_cons0 (p : List Int) (s : Nat → Int) (n : Nat) :
    applyShift (0 :: p) s n = applyShift p (fun m => s (m + 1)) n := by
  show (0 : Int) * s n + applyShift p (fun m => s (m + 1)) n
     = applyShift p (fun m => s (m + 1)) n
  rw [zero_mul, zero_add]

/-- **Convolution = shift-operator composition.**  `applyShift (conv p q) s = applyShift p (applyShift q s)`. -/
theorem applyShift_conv (p q : List Int) (s : Nat → Int) :
    ∀ n, applyShift (conv p q) s n = applyShift p (applyShift q s) n := by
  induction p generalizing s with
  | nil => intro n; rfl
  | cons a p ih =>
    intro n
    show applyShift (addL (smulL a q) (0 :: conv p q)) s n
       = a * applyShift q s n + applyShift p (fun m => applyShift q s (m + 1)) n
    rw [applyShift_addL (smulL a q) (0 :: conv p q) s n, applyShift_smulL a q s n,
        applyShift_cons0 (conv p q) s n, ih (fun m => s (m + 1)) n,
        applyShift_congr p (u := applyShift q (fun m => s (m + 1)))
          (v := fun m => applyShift q s (m + 1)) (fun m => applyShift_shift q s m) n]

/-- ★ **`Δ` is a shift operator: `applyShift [-1,1] = Δ`.**  `(E − I)s(n) = s(n+1) − s(n)`.
    The mirror of `applyOp_shift` (`E = applyOp [1,1]`). -/
theorem applyShift_diffBase (s : Nat → Int) (n : Nat) :
    applyShift [-1, 1] s n = diffZ s n := by
  show (-1) * s n + (1 * s (n + 1) + 0) = s (n + 1) - s n
  rw [neg_mul, Int.one_mul, Int.one_mul, Int.add_zero, Int.sub_eq_add_neg, add_comm]

/-- The `k`-fold difference `Δᵏ` as a *shift* operator: `Δᵏ = (E−I)ᵏ`, built by
    convolving `[-1,1]` with itself `k` times. -/
def dPow : Nat → List Int
  | 0   => [1]
  | i+1 => conv [-1, 1] (dPow i)

/-- ★ **`Δᵏ` as a shift operator computes the `k`-th difference.**  `applyShift (dPow k)
    s n = Δᵏs(n) = liftKZ k s n` — the difference is a polynomial in the shift `E`.  The
    dual of `applyOp_ePow`, and the bridge for C-D's forward direction. -/
theorem applyShift_dPow (s : Nat → Int) : ∀ i n,
    applyShift (dPow i) s n = liftKZ i s n
  | 0,   n => by show 1 * s n + 0 = s n; rw [Int.one_mul, Int.add_zero]
  | i+1, n => by
    show applyShift (conv [-1, 1] (dPow i)) s n = liftKZ (i + 1) s n
    rw [applyShift_conv [-1, 1] (dPow i) s n, applyShift_diffBase (applyShift (dPow i) s) n]
    show applyShift (dPow i) s (n + 1) - applyShift (dPow i) s n = liftKZ (i + 1) s n
    rw [applyShift_dPow s i (n + 1), applyShift_dPow s i n]
    rfl

/-! ## §11 — C-D forward: C-finite ⟹ a monic shift recurrence -/

/-- The shift-operator for a difference combination: `Σ_{i<k} cᵢ · Δⁱ = Σ_{i<k} cᵢ · dPow i`. -/
def sCombo (c : Nat → Int) : Nat → List Int
  | 0   => []
  | k+1 => addL (sCombo c k) (smulL (c k) (dPow k))

/-- `applyShift (sCombo c k) s n = Σ_{i<k} cᵢ Δⁱs(n) = linComb c s k n` — the shift-operator
    `sCombo` realizes the difference combination (each `dPow i` realizes `Δⁱ`). -/
theorem applyShift_sCombo (c : Nat → Int) (s : Nat → Int) : ∀ k n,
    applyShift (sCombo c k) s n = linComb c s k n
  | 0,   _ => rfl
  | k+1, n => by
    show applyShift (addL (sCombo c k) (smulL (c k) (dPow k))) s n
       = linComb c s k n + c k * liftKZ k s n
    rw [applyShift_addL (sCombo c k) (smulL (c k) (dPow k)) s n,
        applyShift_smulL (c k) (dPow k) s n, applyShift_dPow s k n, applyShift_sCombo c s k n]

/-- `dPow k` is monic of degree `k`: `dPow k = lo ++ [v]` with `v = 1`, `|lo| = k`
    (`Δᵏ = (E−I)ᵏ` has leading `E`-coefficient `1`). -/
theorem dPow_eq_snoc : ∀ k, ∃ lo v, dPow k = lo ++ [v] ∧ v = 1 ∧ lo.length = k
  | 0   => ⟨[], 1, rfl, rfl, rfl⟩
  | k+1 => by
    obtain ⟨lo, v, he, hv, hl⟩ := dPow_eq_snoc k
    obtain ⟨r, w, hc, hw, hrl⟩ := conv_snoc [-1] 1 lo v
    refine ⟨r, w, ?_, ?_, ?_⟩
    · show conv [-1, 1] (dPow k) = r ++ [w]
      rw [he]; exact hc
    · rw [hw, hv, Int.one_mul]
    · rw [hrl, hl]; exact Nat.add_comm 1 k

/-- `|sCombo c k| ≤ k` — the difference combination has degree `< k`, so its shift-list is
    shorter than `dPow k` (length `k+1`). -/
theorem sCombo_length_le (c : Nat → Int) : ∀ k, (sCombo c k).length ≤ k
  | 0   => Nat.le_refl 0
  | k+1 => by
    obtain ⟨lo, v, he, _, hl⟩ := dPow_eq_snoc k
    have hsl : (smulL (c k) (dPow k)).length = k + 1 := by
      rw [length_smulL, he, length_snoc, hl]
    have hle : (sCombo c k).length ≤ (smulL (c k) (dPow k)).length := by
      rw [hsl]; exact Nat.le_succ_of_le (sCombo_length_le c k)
    have heq : (sCombo c (k+1)).length = k + 1 := by
      show (addL (sCombo c k) (smulL (c k) (dPow k))).length = k + 1
      rw [length_addL_right_ge (sCombo c k) (smulL (c k) (dPow k)) hle, hsl]
    exact Nat.le_of_eq heq

end E213.Lib.Math.Cauchy.CFiniteRing
