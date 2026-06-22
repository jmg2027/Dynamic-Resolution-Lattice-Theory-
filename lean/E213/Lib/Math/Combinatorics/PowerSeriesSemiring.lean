import E213.Meta.Nat.Convolution213
import E213.Lib.Math.Combinatorics.GeneratingFunction
import E213.Lib.Math.Probability.Limit.ConvolveProfile
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# PowerSeriesSemiring — welding the repo's Cauchy products into one formal-power-series semiring

`generating_functions.md` names the precise missing leg: the repo defines the Cauchy
product **three** times and never welds them —

  * `Combinatorics.GeneratingFunction.convolution` on `CoeffSeq := Nat → Nat`
    (the `let rec aux` sum, proving only `(1·f)₀ = f₀`),
  * `Meta.Nat.Convolution213.conv` on `Nat → Nat` (the `sumMap`-over-`natSplits`
    form — this one **already carries the full pointwise semiring**: `conv_comm`,
    `conv_assoc`, `conv_add_left`/`conv_add_right`, two-sided unit `delta` via
    `conv_delta_left`/`conv_delta_right`, scalar linearity, and the Leibniz
    derivation), and
  * `Probability.Limit.ConvolveProfile.conv`/`⋆` on `Profile := List Nat`
    (the one-row recursion, carrying the **proven character laws**
    `mass_conv : mass (f⋆g) = mass f · mass g` and `momentNum_conv`).

This file is the weld.  Everything is stated **pointwise** (`∀ n, … n = … n`) so it
stays `funext`-free and ∅-axiom (extensional function equality on `Nat → Nat` would need
`funext`, which leaks `Quot.sound` — forbidden):

1. **`GeneratingFunction.convolution = Convolution213.conv`** (pointwise,
   `gfConv_eq_conv`, both `= Σ_{i≤n} fᵢ·g_{n-i}` via `conv_eq_cauchy`) and
   **`GeneratingFunction.one = Convolution213.delta`** (`gfOne_eq_delta`).  This
   transports the entire `Convolution213` semiring onto the combinatorial
   `convolution`/`one`: the semiring laws (`conv_comm'`, `conv_assoc'`,
   `conv_one_left`/`conv_one_right`, `conv_add_distrib_left`/`_right`,
   `conv_zero_left`/`_right`, `addSeq_comm`/`addSeq_assoc`/`addSeq_zero`) now hold on
   `GeneratingFunction.convolution` with the degree-1 generator `xVar` the grading
   variable.

2. **The character homomorphisms on `CoeffSeq`.**  `mass N f := Σ_{k<N} f k` is the
   `x ↦ 1` evaluation character (additive over `+`: `mass_addSeq`); `momentDeg N f :=
   Σ_{k<N} k·f k` is the `x·d/dx` degree character (additive: `momentDeg_addSeq`).  The
   **multiplicative** half (`mass (f⋆g) = mass f · mass g`) is the load-bearing law and
   is supplied through the list bridge, re-using the proven `ConvolveProfile.mass_conv`.

3. **The list→sequence weld map** `toCoeffSeq : Profile → CoeffSeq := nth`, commuting
   with the two convolutions: `toCoeffSeq (f ⋆ g) n = Convolution213.conv (toCoeffSeq f)
   (toCoeffSeq g) n` (`toCoeffSeq_conv`).  Bridged through
   `ConvolveProfile.mass f = sumTo f.length (toCoeffSeq f)` (`mass_eq_sumTo`), this
   transports `ConvolveProfile.mass_conv` to the multiplicative character of the welded
   product (`mass_toCoeffSeq_conv`) — no re-derivation of the product law.

## Honest residual

The semiring is **pointwise**: `conv_comm' : ∀ n, convolution f g n = convolution g f n`,
not `convolution f g = convolution g f`.  Extensional ring equality on `Nat → Nat`
requires `funext` (= `Quot.sound`, forbidden by the ∅-axiom contract), so the algebraic
structure is the pointwise one — the honest ∅-axiom carrier, and exactly what every
downstream coefficient computation uses.  The general (support-free) `mass`
multiplicativity directly on `CoeffSeq` would need a degree bound on the truncation `N`;
the bridged list form is total (mass over the exact lengths) and is the complete
load-bearing statement.  The analytic generating function (radius of convergence,
closed-form value as a real map) remains the `Real213`-cut residue, unbuilt — same
boundary as `zeta_euler.md`/`exponential.md`.  Both noted in `generating_functions.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.Combinatorics.PowerSeriesSemiring

open E213.Meta.Nat.Convolution213
  (conv natSplits sumMap conv_zero conv_comm conv_assoc conv_add_left conv_add_right
   conv_delta_left conv_delta_right delta sumMap_congr sumMap_zero conv_peelL shiftL
   conv_congr_left nth)
open E213.Lib.Math.Combinatorics.GeneratingFunction (CoeffSeq convolution one xVar)
open E213.Lib.Math.Probability.Limit.ConvolveProfile (Profile mass scale addL)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-! ## 0. Both Cauchy products are the partial-sum `Σ_{i≤n} fᵢ·g_{n-i}` -/

/-- `(n+1) − i = (n − i) + 1` for `i ≤ n` — pure `Nat`, by induction (no `omega`,
    which would leak `propext`/`Quot.sound`). -/
theorem succ_sub_eq : ∀ (n i : Nat), i ≤ n → (n + 1) - i = (n - i) + 1
  | _,   0,   _ => rfl
  | 0,   _+1, h => nomatch h
  | n+1, i+1, h => by
      rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
      exact succ_sub_eq n i (Nat.le_of_succ_le_succ h)

/-- `sumTo` congruence over the index range `[0, m)` (no `funext`). -/
theorem sumTo_congr_lt {g1 g2 : CoeffSeq} :
    ∀ m, (∀ i, i < m → g1 i = g2 i) → sumTo m g1 = sumTo m g2
  | 0, _ => rfl
  | m + 1, h => by
      show sumTo m g1 + g1 m = sumTo m g2 + g2 m
      rw [sumTo_congr_lt m (fun i hi => h i (Nat.lt_succ_of_lt hi)),
          h m (Nat.lt_succ_self m)]

/-- `Convolution213.conv f g n = Σ_{i=0}^{n} fᵢ · g_{n−i}` — the `sumMap`-over-cuts form
    collapsed to a `sumTo`, by repeatedly peeling the **right** end (`conv_peelR`). -/
theorem conv_eq_cauchy (f g : CoeffSeq) :
    ∀ n, conv f g n = sumTo (n + 1) (fun i => f i * g (n - i))
  | 0 => by rw [conv_zero]; show f 0 * g 0 = 0 + f 0 * g 0; rw [Nat.zero_add]
  | n + 1 => by
      rw [E213.Meta.Nat.Convolution213.conv_peelR f g n, conv_eq_cauchy f (shiftL g) n,
          sumTo_succ]
      show f (n+1) * g 0 + sumTo (n+1) (fun i => f i * shiftL g (n - i))
         = sumTo (n+1) (fun i => f i * g (n + 1 - i)) + f (n+1) * g (n+1 - (n+1))
      rw [Nat.sub_self (n+1)]
      have hcongr : sumTo (n+1) (fun i => f i * shiftL g (n - i))
                  = sumTo (n+1) (fun i => f i * g (n + 1 - i)) :=
        sumTo_congr_lt (n+1) (fun i hi => by
          show f i * g (n - i + 1) = f i * g (n + 1 - i)
          have hle : i ≤ n := Nat.lt_succ_iff.mp hi
          rw [succ_sub_eq n i hle])
      rw [hcongr, Nat.add_comm]

/-- The inner `convolution.aux` is the same partial Cauchy sum (peeling from index `k`
    down to `0`). -/
theorem aux_eq_sum (f g : CoeffSeq) (n : Nat) :
    ∀ k, convolution.aux f g n k = sumTo (k + 1) (fun i => f i * g (n - i))
  | 0 => by show f 0 * g (n - 0) = 0 + f 0 * g (n - 0); rw [Nat.zero_add]
  | k + 1 => by
      show f (k+1) * g (n - (k+1)) + convolution.aux f g n k
         = sumTo (k+1+1) (fun i => f i * g (n - i))
      rw [aux_eq_sum f g n k, sumTo_succ]
      show f (k+1) * g (n - (k+1)) + sumTo (k+1) (fun i => f i * g (n - i))
         = sumTo (k+1) (fun i => f i * g (n - i)) + f (k+1) * g (n - (k+1))
      rw [Nat.add_comm]

/-- `GeneratingFunction.convolution f g n = Σ_{i=0}^{n} fᵢ · g_{n−i}`. -/
theorem convolution_eq_cauchy (f g : CoeffSeq) (n : Nat) :
    convolution f g n = sumTo (n + 1) (fun i => f i * g (n - i)) :=
  aux_eq_sum f g n n

/-! ## 1. The weld: `GeneratingFunction.convolution` IS `Convolution213.conv` -/

/-- ★★ **Weld** — the two `Σ_{i+j=n} fᵢ·gⱼ` definitions coincide coefficient-by-coefficient:
    `GeneratingFunction.convolution f g n = Convolution213.conv f g n`. -/
theorem gfConv_eq_conv (f g : CoeffSeq) (n : Nat) :
    convolution f g n = conv f g n := by
  rw [convolution_eq_cauchy, conv_eq_cauchy]

/-- ★ **Unit weld** — `GeneratingFunction.one n = Convolution213.delta n`, pointwise. -/
theorem gfOne_eq_delta : ∀ n, one n = delta n
  | 0     => rfl
  | _ + 1 => rfl

/-! ## 2. The semiring laws on `GeneratingFunction.convolution` (pointwise, funext-free)

Transported through the weld from the canonical `Convolution213` semiring.  Stated
pointwise — extensional function equality would need `funext`. -/

/-- Pointwise sum of coefficient sequences (the additive structure). -/
def addSeq (f g : CoeffSeq) : CoeffSeq := fun n => f n + g n

/-- The zero series. -/
def zeroSeq : CoeffSeq := fun _ => 0

/-- right-congruence for `conv` (derived from `conv_comm` + `conv_congr_left`). -/
theorem conv_congr_right {f g1 g2 : CoeffSeq} (he : ∀ i, g1 i = g2 i) (n : Nat) :
    conv f g1 n = conv f g2 n := by
  rw [conv_comm f g1, conv_comm f g2]; exact conv_congr_left he n

/-- ★ **Commutativity**: `(f ⋆ g)ₙ = (g ⋆ f)ₙ`. -/
theorem conv_comm' (f g : CoeffSeq) (n : Nat) :
    convolution f g n = convolution g f n := by
  rw [gfConv_eq_conv, gfConv_eq_conv, conv_comm]

/-- ★ **Associativity**: `((f ⋆ g) ⋆ h)ₙ = (f ⋆ (g ⋆ h))ₙ`. -/
theorem conv_assoc' (f g h : CoeffSeq) (n : Nat) :
    convolution (fun k => convolution f g k) h n
      = convolution f (fun k => convolution g h k) n := by
  rw [gfConv_eq_conv (fun k => convolution f g k) h,
      gfConv_eq_conv f (fun k => convolution g h k),
      conv_congr_left (f1 := fun k => convolution f g k) (f2 := fun k => conv f g k)
        (gfConv_eq_conv f g) n,
      conv_congr_right (f := f) (g1 := fun k => convolution g h k)
        (g2 := fun k => conv g h k) (gfConv_eq_conv g h) n]
  exact conv_assoc f g h n

/-- ★ **Left unit**: `(1 ⋆ f)ₙ = fₙ`. -/
theorem conv_one_left (f : CoeffSeq) (n : Nat) : convolution one f n = f n := by
  rw [gfConv_eq_conv, conv_congr_left (f1 := one) (f2 := delta) gfOne_eq_delta n,
      conv_delta_left]

/-- ★ **Right unit**: `(f ⋆ 1)ₙ = fₙ`. -/
theorem conv_one_right (f : CoeffSeq) (n : Nat) : convolution f one n = f n := by
  rw [conv_comm', conv_one_left]

/-- ★ **Left distributivity**: `((f₁ + f₂) ⋆ g)ₙ = (f₁ ⋆ g)ₙ + (f₂ ⋆ g)ₙ`. -/
theorem conv_add_distrib_left (f1 f2 g : CoeffSeq) (n : Nat) :
    convolution (addSeq f1 f2) g n = convolution f1 g n + convolution f2 g n := by
  rw [gfConv_eq_conv, gfConv_eq_conv, gfConv_eq_conv]; exact conv_add_left f1 f2 g n

/-- ★ **Right distributivity**: `(f ⋆ (g₁ + g₂))ₙ = (f ⋆ g₁)ₙ + (f ⋆ g₂)ₙ`. -/
theorem conv_add_distrib_right (f g1 g2 : CoeffSeq) (n : Nat) :
    convolution f (addSeq g1 g2) n = convolution f g1 n + convolution f g2 n := by
  rw [gfConv_eq_conv, gfConv_eq_conv, gfConv_eq_conv]; exact conv_add_right f g1 g2 n

/-- ★ **Zero annihilates (left)**: `(0 ⋆ f)ₙ = 0`. -/
theorem conv_zero_left (f : CoeffSeq) (n : Nat) : convolution zeroSeq f n = 0 := by
  rw [gfConv_eq_conv]
  show sumMap (fun p => (0 : Nat) * f p.2) (natSplits n) = 0
  rw [sumMap_congr (h2 := fun _ => 0) (fun p => Nat.zero_mul (f p.2)) (natSplits n)]
  exact sumMap_zero (natSplits n)

/-- ★ **Zero annihilates (right)**: `(f ⋆ 0)ₙ = 0`. -/
theorem conv_zero_right (f : CoeffSeq) (n : Nat) : convolution f zeroSeq n = 0 := by
  rw [conv_comm', conv_zero_left]

/-- Pointwise `+` is commutative. -/
theorem addSeq_comm (f g : CoeffSeq) (n : Nat) : addSeq f g n = addSeq g f n :=
  Nat.add_comm (f n) (g n)

/-- Pointwise `+` is associative. -/
theorem addSeq_assoc (f g h : CoeffSeq) (n : Nat) :
    addSeq (addSeq f g) h n = addSeq f (addSeq g h) n :=
  Nat.add_assoc (f n) (g n) (h n)

/-- `0` is the additive unit. -/
theorem addSeq_zero (f : CoeffSeq) (n : Nat) : addSeq f zeroSeq n = f n :=
  Nat.add_zero (f n)

/-! ## 3. The character homomorphisms on `CoeffSeq` -/

/-- A 4-term commutative rearrangement, ∅-axiom. -/
private theorem add4comm (a b c d : Nat) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc, Nat.add_left_comm b c d, ← Nat.add_assoc]

/-- **Total-count / evaluation-at-`x=1` character**, truncated to degree `< N`:
    `mass N f = Σ_{k<N} f k` (the generating function read at `x = 1`). -/
def massN (N : Nat) (f : CoeffSeq) : Nat := sumTo N f

/-- **Degree / first-moment character**, truncated: `momentDeg N f = Σ_{k<N} k·f k`
    (the `x·d/dx` first moment). -/
def momentDeg (N : Nat) (f : CoeffSeq) : Nat := sumTo N (fun k => k * f k)

/-- ★ `massN` is **additive** over the pointwise sum — the evaluation character's
    additive half (`x ↦ 1` is a `+`-homomorphism). -/
theorem massN_addSeq (f g : CoeffSeq) :
    ∀ N, massN N (addSeq f g) = massN N f + massN N g
  | 0     => rfl
  | N + 1 => by
      have ih : sumTo N (addSeq f g) = sumTo N f + sumTo N g := massN_addSeq f g N
      show sumTo N (addSeq f g) + addSeq f g N = (sumTo N f + f N) + (sumTo N g + g N)
      rw [ih]; show (sumTo N f + sumTo N g) + (f N + g N) = (sumTo N f + f N) + (sumTo N g + g N)
      rw [add4comm]

/-- ★ `momentDeg` is **additive** over the pointwise sum — the degree character's
    additive half. -/
theorem momentDeg_addSeq (f g : CoeffSeq) :
    ∀ N, momentDeg N (addSeq f g) = momentDeg N f + momentDeg N g
  | 0     => rfl
  | N + 1 => by
      have ih : sumTo N (fun k => k * addSeq f g k)
              = sumTo N (fun k => k * f k) + sumTo N (fun k => k * g k) :=
        momentDeg_addSeq f g N
      show sumTo N (fun k => k * addSeq f g k) + N * addSeq f g N
         = (sumTo N (fun k => k * f k) + N * f N) + (sumTo N (fun k => k * g k) + N * g N)
      rw [ih]
      show (sumTo N (fun k => k * f k) + sumTo N (fun k => k * g k)) + N * (f N + g N)
         = (sumTo N (fun k => k * f k) + N * f N) + (sumTo N (fun k => k * g k) + N * g N)
      rw [Nat.mul_add, add4comm]

/-! ## 4. The list→sequence weld map and the transported multiplicative character -/

/-- The weld map `Profile → CoeffSeq`: read a finite list as a coefficient sequence
    (`0` past the end).  This is `Convolution213.nth`, identifying the two finite
    packagings of a generating function. -/
def toCoeffSeq (f : Profile) : CoeffSeq := nth f

theorem nth_nil (k : Nat) : nth ([] : Profile) k = 0 := rfl

/-- `toCoeffSeq` carries the pointwise sum: `nth (addL f g) = nth f + nth g`. -/
theorem nth_addL : ∀ (f g : Profile) (k : Nat), nth (addL f g) k = nth f k + nth g k
  | [],     g,      k     => by rw [addL, nth_nil, Nat.zero_add]
  | a :: f, [],     k     => by
      rw [show addL (a :: f) [] = a :: f from rfl, nth_nil, Nat.add_zero]
  | _ :: _, _ :: _, 0     => rfl
  | _ :: f, _ :: g, k + 1 => by show nth (addL f g) k = nth f k + nth g k; exact nth_addL f g k

/-- `toCoeffSeq` carries the scale: `nth (scale c f) = c · nth f`. -/
theorem nth_scale : ∀ (c : Nat) (f : Profile) (k : Nat), nth (scale c f) k = c * nth f k
  | c, [],     _     => by show (0 : Nat) = c * 0; rw [Nat.mul_zero]
  | _, _ :: _, 0     => rfl
  | c, _ :: f, k + 1 => by show nth (scale c f) k = c * nth f k; exact nth_scale c f k

/-- `shiftL (nth (a :: f)) = nth f` pointwise (drop the head). -/
theorem shiftL_nth_cons (a : Nat) (f : Profile) : ∀ k, shiftL (nth (a :: f)) k = nth f k :=
  fun _ => rfl

/-- ★★ **The weld of the two convolutions** — the list `⋆` maps to the canonical `conv`:
    `toCoeffSeq (f ⋆ g) n = Convolution213.conv (toCoeffSeq f) (toCoeffSeq g) n`, pointwise.
    Distribute the head over `g` (`addL`/`scale` = the left peel `conv_peelL`) and shift the
    tail (`0 :: ·`), matching `natSplits`' left build. -/
theorem toCoeffSeq_conv :
    ∀ (f g : Profile) (n : Nat),
      toCoeffSeq (E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g) n
        = conv (toCoeffSeq f) (toCoeffSeq g) n
  | [],     g, n => by
      show nth (E213.Lib.Math.Probability.Limit.ConvolveProfile.conv [] g) n
         = conv (nth ([] : Profile)) (nth g) n
      rw [show E213.Lib.Math.Probability.Limit.ConvolveProfile.conv [] g = [] from rfl,
          nth_nil n]
      symm
      show conv (nth ([] : Profile)) (nth g) n = 0
      show sumMap (fun p => nth ([] : Profile) p.1 * nth g p.2) (natSplits n) = 0
      rw [sumMap_congr (h2 := fun _ => 0)
            (fun p => by rw [nth_nil p.1, Nat.zero_mul]) (natSplits n)]
      exact sumMap_zero (natSplits n)
  | a :: f, g, n => by
      show nth (addL (scale a g)
              ((0 : Nat) :: E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g)) n
         = conv (nth (a :: f)) (nth g) n
      rw [nth_addL (scale a g)
            ((0 : Nat) :: E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g) n,
          nth_scale a g n]
      cases n with
      | zero =>
          rw [conv_zero]
          show a * nth g 0
             + nth ((0 : Nat) :: E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g) 0
             = nth (a :: f) 0 * nth g 0
          show a * nth g 0 + 0 = a * nth g 0
          rw [Nat.add_zero]
      | succ m =>
          rw [conv_peelL (nth (a :: f)) (nth g) m]
          show a * nth g (m+1)
             + nth ((0 : Nat) :: E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g) (m+1)
             = nth (a :: f) 0 * nth g (m+1) + conv (shiftL (nth (a :: f))) (nth g) m
          show a * nth g (m+1)
             + nth (E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g) m
             = a * nth g (m+1) + conv (shiftL (nth (a :: f))) (nth g) m
          rw [conv_congr_left (f1 := shiftL (nth (a :: f))) (f2 := nth f)
                (shiftL_nth_cons a f) m]
          exact congrArg (fun t => a * nth g (m+1) + t) (toCoeffSeq_conv f g m)

/-- A head-peel for `sumTo`: `Σ_{k<n+1} g k = g 0 + Σ_{k<n} g (k+1)`. -/
theorem sumTo_peel_head (g : CoeffSeq) :
    ∀ n, sumTo (n + 1) g = g 0 + sumTo n (fun k => g (k + 1))
  | 0     => by show (0 + g 0) = g 0 + 0; rw [Nat.zero_add, Nat.add_zero]
  | n + 1 => by
      show sumTo (n+1) g + g (n+1) = g 0 + (sumTo n (fun k => g (k+1)) + g (n+1))
      rw [sumTo_peel_head g n, Nat.add_assoc]

/-- **Bridge** — `ConvolveProfile.mass` (the list total) is the truncated `massN` of the
    welded sequence over the list's length: `mass f = Σ_{k<|f|} (toCoeffSeq f) k`. -/
theorem mass_eq_sumTo : ∀ f : Profile, mass f = sumTo f.length (toCoeffSeq f)
  | []     => rfl
  | a :: f => by
      show a + mass f = sumTo (f.length + 1) (nth (a :: f))
      rw [sumTo_peel_head (nth (a :: f)) f.length, mass_eq_sumTo f]
      show a + sumTo f.length (nth f)
         = nth (a :: f) 0 + sumTo f.length (fun k => nth (a :: f) (k + 1))
      rfl

/-- ★★★ **The multiplicative character on the welded carrier** — `massN` (evaluation at
    `x = 1`) is **multiplicative under the convolution product**:
    `Σ_{k<|f⋆g|} (toCoeffSeq (f⋆g)) k = (Σ_{k<|f|} toCoeffSeq f) · (Σ_{k<|g|} toCoeffSeq g)`.
    This is the `× ↦ ·` character — the "evaluate the generating function at `x=1`" map is
    a semiring homomorphism — transported from the proven `ConvolveProfile.mass_conv`
    through the weld, with **no re-derivation** of the product law. -/
theorem massN_toCoeffSeq_conv (f g : Profile) :
    sumTo (E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g).length
        (toCoeffSeq (E213.Lib.Math.Probability.Limit.ConvolveProfile.conv f g))
      = sumTo f.length (toCoeffSeq f) * sumTo g.length (toCoeffSeq g) := by
  rw [← mass_eq_sumTo, ← mass_eq_sumTo, ← mass_eq_sumTo]
  exact E213.Lib.Math.Probability.Limit.ConvolveProfile.mass_conv f g

/-- ★★ **The convolution semiring, assembled** (pointwise) — `(CoeffSeq, addSeq, convolution,
    zeroSeq, one)` satisfies the commutative-semiring laws coefficient-by-coefficient, with
    `xVar` the degree-1 grading generator and `massN` a multiplicative `+`-homomorphism
    character (the `x ↦ 1` evaluation).  This is `generating_functions.md`'s named missing
    leg, closed pointwise (funext-free, ∅-axiom). -/
theorem power_series_semiring (f g h : CoeffSeq) (n : Nat) :
    convolution f g n = convolution g f n
    ∧ convolution (fun k => convolution f g k) h n
        = convolution f (fun k => convolution g h k) n
    ∧ convolution one f n = f n
    ∧ convolution f one n = f n
    ∧ convolution (addSeq f g) h n = convolution f h n + convolution g h n
    ∧ convolution f (addSeq g h) n = convolution f g n + convolution f h n
    ∧ convolution zeroSeq f n = 0 :=
  ⟨conv_comm' f g n, conv_assoc' f g h n, conv_one_left f n, conv_one_right f n,
   conv_add_distrib_left f g h n, conv_add_distrib_right f g h n, conv_zero_left f n⟩

end E213.Lib.Math.Combinatorics.PowerSeriesSemiring
