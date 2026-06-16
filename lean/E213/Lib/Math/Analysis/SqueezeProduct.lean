import E213.Lib.Math.Analysis.LimitArithmetic
import E213.Lib.Math.Analysis.ModulusConvergence
import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Meta.Nat.Max213
import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.FloorLog

/-!
# Squeeze + bounded-product limit laws on `distMet` (∅-axiom, Tier-C)

Extends `LimitArithmetic`.  Two new limit laws on the concrete `distMet L0`
metric (Nat-valued sequences), each with the modulus **computed**.
-/

namespace E213.Lib.Math.Analysis.SqueezeProduct

open E213.Lib.Math.Analysis.UniformLimitContinuous
  (distN distN_tri distN_symm closeN distMet le_sub_add sub_le_of_le_add)
open E213.Lib.Math.Analysis.ModulusConvergence (ConvergesWith const_converges)
open E213.Lib.Math.Analysis.LimitArithmetic (closeN_add_core)

/-! ## 1. Pure-`Nat` betweenness fact for `distN` -/

/-- **Betweenness bound.**  If `a ≤ c ≤ b` then `|c − L| ≤ |a − L| + |b − L|`.

    Pure truncated-`Nat`.  `distN c L = (c − L) + (L − c)`; with `a ≤ c ≤ b`:
    `c − L ≤ b − L ≤ distN b L` and `L − c ≤ L − a ≤ distN a L`. -/
theorem distN_between (a b c L : Nat) (hac : a ≤ c) (hcb : c ≤ b) :
    distN c L ≤ distN a L + distN b L := by
  -- c − L ≤ b − L  (pure: via sub_le_of_le_add, using c ≤ b ≤ (b−L)+L)
  have h1 : c - L ≤ b - L := by
    apply sub_le_of_le_add
    exact Nat.le_trans hcb (le_sub_add L b)
  -- L − c ≤ L − a  (pure: via sub_le_of_le_add, using L ≤ (L−a)+a ≤ (L−a)+c)
  have h2 : L - c ≤ L - a := by
    apply sub_le_of_le_add
    exact Nat.le_trans (le_sub_add a L) (Nat.add_le_add_left hac (L - a))
  -- b − L ≤ distN b L = (b − L) + (L − b)
  have hb : b - L ≤ distN b L := by
    show b - L ≤ (b - L) + (L - b)
    exact Nat.le_add_right _ _
  -- L − a ≤ distN a L = (a − L) + (L − a)
  have ha : L - a ≤ distN a L := by
    show L - a ≤ (a - L) + (L - a)
    exact Nat.le_add_left _ _
  -- distN c L = (c − L) + (L − c) ≤ (b − L) + (L − a) ≤ distN b L + distN a L
  have hcombo : (c - L) + (L - c) ≤ (b - L) + (L - a) :=
    Nat.add_le_add h1 h2
  have hcombo2 : (b - L) + (L - a) ≤ distN b L + distN a L :=
    Nat.add_le_add hb ha
  have hchain : (c - L) + (L - c) ≤ distN b L + distN a L :=
    Nat.le_trans hcombo hcombo2
  -- distN c L = (c − L) + (L − c); rewrite RHS to distN a L + distN b L
  show (c - L) + (L - c) ≤ distN a L + distN b L
  rw [Nat.add_comm (distN a L) (distN b L)]
  exact hchain

/-! ## 2. ★ `squeeze_converges` -/

/-- **★ `squeeze_converges` (∅-axiom, modulus computed).**  On `distMet L0`,
    if `a ≤ c ≤ b` pointwise and both `a → L` (modulus `ra`) and `b → L`
    (modulus `rb`) with the **same** limit `L`, then `c → L` with the computed
    modulus `m ↦ max (ra (m+1)) (rb (m+1))`.

    For `n` past both bounds, `a n` and `b n` are each `1/2^(m+1)`-near `L`;
    betweenness `a n ≤ c n ≤ b n` gives `distN (c n) L ≤ distN (a n) L +
    distN (b n) L`, and two halves make a whole (`closeN_add_core`). -/
theorem squeeze_converges {L0 : Nat} {a b c : Nat → Nat} {L : Nat}
    {ra rb : Nat → Nat}
    (hbtw : ∀ n, a n ≤ c n ∧ c n ≤ b n)
    (ha : ConvergesWith (distMet L0) a L ra)
    (hb : ConvergesWith (distMet L0) b L rb) :
    ConvergesWith (distMet L0) c L
      (fun m => Nat.max (ra (m + 1)) (rb (m + 1))) := by
  intro m n hn
  have hna : ra (m + 1) ≤ n :=
    Nat.le_trans (E213.Meta.Nat.Max213.le_max_left (ra (m + 1)) (rb (m + 1))) hn
  have hnb : rb (m + 1) ≤ n :=
    Nat.le_trans (E213.Meta.Nat.Max213.le_max_right (ra (m + 1)) (rb (m + 1))) hn
  -- closeN at scale m+1 for a and b
  have ca : closeN L0 (m + 1) (a n) L := ha (m + 1) n hna
  have cb : closeN L0 (m + 1) (b n) L := hb (m + 1) n hnb
  have hXlt : 2 ^ (m + 1) * distN (a n) L < 2 ^ (L0 + 1) := ca
  have hYlt : 2 ^ (m + 1) * distN (b n) L < 2 ^ (L0 + 1) := cb
  -- two-halves-make-whole on the betweenness bound
  have hcore : 2 ^ m * (distN (a n) L + distN (b n) L) < 2 ^ (L0 + 1) :=
    closeN_add_core L0 m (distN (a n) L) (distN (b n) L) hXlt hYlt
  -- betweenness: distN (c n) L ≤ distN (a n) L + distN (b n) L
  have hle : distN (c n) L ≤ distN (a n) L + distN (b n) L :=
    distN_between (a n) (b n) (c n) L (hbtw n).1 (hbtw n).2
  show closeN L0 m (c n) L
  show 2 ^ m * distN (c n) L < 2 ^ (L0 + 1)
  have hmono : 2 ^ m * distN (c n) L
      ≤ 2 ^ m * (distN (a n) L + distN (b n) L) :=
    Nat.mul_le_mul_left _ hle
  exact Nat.lt_of_le_of_lt hmono hcore

/-! ## 3. Multiplicative-distance facts (pure `Nat`) -/

/-- `k * x − k * y = k * (x − y)` — unconditional, ∅-axiom.  `Nat.le_total`
    casework: when `x ≤ y` both sides are `0`; when `y ≤ x`, `mul_sub_213`. -/
theorem mul_sub_uncond (k x y : Nat) : k * x - k * y = k * (x - y) := by
  rcases Nat.le_total x y with hxy | hyx
  · -- x ≤ y: k*x ≤ k*y so LHS = 0; x - y = 0 so RHS = k*0 = 0
    have hkle : k * x ≤ k * y := Nat.mul_le_mul_left k hxy
    -- pure `p ≤ q → p - q = 0`: `sub_le_of_le_add` (p ≤ 0 + q) then `eq_zero_of_le_zero`
    have hL : k * x - k * y = 0 :=
      Nat.eq_zero_of_le_zero
        (sub_le_of_le_add (Nat.le_trans hkle (Nat.le_of_eq (Nat.zero_add (k * y)).symm)))
    have hR : x - y = 0 :=
      Nat.eq_zero_of_le_zero
        (sub_le_of_le_add (Nat.le_trans hxy (Nat.le_of_eq (Nat.zero_add y).symm)))
    rw [hL, hR, Nat.mul_zero]
  · -- y ≤ x: direct
    exact E213.Meta.Nat.Gcd213.mul_sub_213 k y x hyx

/-- **`distN_mul_left`**: `distN (k·x) (k·y) = k · distN x y`.  Both truncated
    legs distribute by `mul_sub_uncond`, then `Nat.left_distrib`. -/
theorem distN_mul_left (k x y : Nat) : distN (k * x) (k * y) = k * distN x y := by
  show (k * x - k * y) + (k * y - k * x) = k * ((x - y) + (y - x))
  rw [mul_sub_uncond k x y, mul_sub_uncond k y x, Nat.left_distrib]

/-! ## 4. ★ `mul_converges_bounded` — bounded-product limit law -/

/-- **`mul_converges_bounded` (∅-axiom, modulus computed).**  On `distMet L0`,
    if `a → A` (mod `ra`), `b → B` (mod `rb`), and the sequences are uniformly
    bounded by `K` (`∀ n, a n ≤ K ∧ b n ≤ K`, and `A ≤ K`, `B ≤ K`), then the
    pointwise product `a · b → A · B` with the **computed** modulus

        m ↦ max (ra (m + j + 1)) (rb (m + j + 1)),   j = floorLog 2 K + 1,

    where `j` is a bit-length of `K` (`K < 2^j`, from `lt_pow_floorLog_succ`).
    The `K`-factor (from the cross-term bound) is absorbed by shifting the
    convergence scale by `j`.

    Proof.  `distN (aₙbₙ) (AB) ≤ distN (aₙbₙ) (aₙB) + distN (aₙB) (AB)`
    (`distN_tri`) `= aₙ·distN bₙ B + B·distN aₙ A` (`distN_mul_left`, the right
    factor commuted) `≤ K·(distN aₙ A + distN bₙ B)`.  With `2^m·K ≤ 2^(m+j)`
    (`K ≤ 2^j`), the bound is `≤ 2^(m+j)·(distN aₙ A + distN bₙ B)`, which is
    `< 2^(L0+1)` by `closeN_add_core` at scale `m+j` from the two convergence
    facts at scale `m+j+1`. -/
theorem mul_converges_bounded_core {L0 : Nat} {a b : Nat → Nat} {A B K j : Nat}
    {ra rb : Nat → Nat}
    (hKle : K ≤ 2 ^ j)
    (hbd : ∀ n, a n ≤ K ∧ b n ≤ K) (hBK : B ≤ K)
    (ha : ConvergesWith (distMet L0) a A ra)
    (hb : ConvergesWith (distMet L0) b B rb) :
    ConvergesWith (distMet L0) (fun n => a n * b n) (A * B)
      (fun m => Nat.max (ra (m + j + 1)) (rb (m + j + 1))) := by
  intro m n hn
  -- extract the two convergence facts at scale m+j+1
  have hna : ra (m + j + 1) ≤ n :=
    Nat.le_trans (E213.Meta.Nat.Max213.le_max_left _ _) hn
  have hnb : rb (m + j + 1) ≤ n :=
    Nat.le_trans (E213.Meta.Nat.Max213.le_max_right _ _) hn
  have ca : closeN L0 (m + j + 1) (a n) A := ha (m + j + 1) n hna
  have cb : closeN L0 (m + j + 1) (b n) B := hb (m + j + 1) n hnb
  have hXlt : 2 ^ (m + j + 1) * distN (a n) A < 2 ^ (L0 + 1) := ca
  have hYlt : 2 ^ (m + j + 1) * distN (b n) B < 2 ^ (L0 + 1) := cb
  -- closeN_add_core at scale m+j (note: (m+j)+1 = m+j+1)
  have hcore : 2 ^ (m + j) * (distN (a n) A + distN (b n) B) < 2 ^ (L0 + 1) :=
    closeN_add_core L0 (m + j) (distN (a n) A) (distN (b n) B) hXlt hYlt
  -- distance decomposition: distN (aₙbₙ)(AB) ≤ aₙ·distN bₙ B + B·distN aₙ A
  -- leg 1: distN (aₙ·bₙ)(aₙ·B) = aₙ · distN bₙ B
  have leg1 : distN (a n * b n) (a n * B) = a n * distN (b n) B :=
    distN_mul_left (a n) (b n) B
  -- leg 2: distN (aₙ·B)(A·B) = distN (B·aₙ)(B·A) = B · distN aₙ A
  have leg2 : distN (a n * B) (A * B) = B * distN (a n) A := by
    rw [Nat.mul_comm (a n) B, Nat.mul_comm A B]
    exact distN_mul_left B (a n) A
  -- triangle
  have htri : distN (a n * b n) (A * B)
      ≤ distN (a n * b n) (a n * B) + distN (a n * B) (A * B) :=
    distN_tri (a n * b n) (a n * B) (A * B)
  rw [leg1, leg2] at htri
  -- htri : distN (aₙbₙ)(AB) ≤ aₙ·distN bₙ B + B·distN aₙ A
  -- bound each cross term by K·(...)
  have hb1 : a n * distN (b n) B ≤ K * distN (b n) B :=
    Nat.mul_le_mul_right _ (hbd n).1
  have hb2 : B * distN (a n) A ≤ K * distN (a n) A :=
    Nat.mul_le_mul_right _ hBK
  have hsum : a n * distN (b n) B + B * distN (a n) A
      ≤ K * distN (b n) B + K * distN (a n) A :=
    Nat.add_le_add hb1 hb2
  -- K·distN bₙ B + K·distN aₙ A = K·(distN aₙ A + distN bₙ B)
  have hfactor : K * distN (b n) B + K * distN (a n) A
      = K * (distN (a n) A + distN (b n) B) := by
    rw [Nat.left_distrib, Nat.add_comm (K * distN (a n) A) (K * distN (b n) B)]
  have hdle : distN (a n * b n) (A * B) ≤ K * (distN (a n) A + distN (b n) B) := by
    rw [← hfactor]
    exact Nat.le_trans htri hsum
  -- now scale by 2^m and absorb K ≤ 2^j into 2^(m+j)
  show closeN L0 m (a n * b n) (A * B)
  show 2 ^ m * distN (a n * b n) (A * B) < 2 ^ (L0 + 1)
  -- 2^m · distN ≤ 2^m · (K · D)
  have step1 : 2 ^ m * distN (a n * b n) (A * B)
      ≤ 2 ^ m * (K * (distN (a n) A + distN (b n) B)) :=
    Nat.mul_le_mul_left _ hdle
  -- 2^m · (K · D) = (2^m · K) · D ≤ (2^m · 2^j) · D = 2^(m+j) · D
  -- (D abbreviates `distN (a n) A + distN (b n) B`)
  have hassoc : 2 ^ m * (K * (distN (a n) A + distN (b n) B))
      = (2 ^ m * K) * (distN (a n) A + distN (b n) B) :=
    (E213.Meta.Nat.PureNat.mul_assoc (2 ^ m) K (distN (a n) A + distN (b n) B)).symm
  have hmK : 2 ^ m * K ≤ 2 ^ m * 2 ^ j := Nat.mul_le_mul_left _ hKle
  have hpow : 2 ^ m * 2 ^ j = 2 ^ (m + j) :=
    (E213.Meta.Nat.PureNat.pow_add 2 m j).symm
  have hmK2 : 2 ^ m * K ≤ 2 ^ (m + j) := by rw [← hpow]; exact hmK
  have step2 : (2 ^ m * K) * (distN (a n) A + distN (b n) B)
      ≤ 2 ^ (m + j) * (distN (a n) A + distN (b n) B) :=
    Nat.mul_le_mul_right _ hmK2
  -- chain: 2^m·distN ≤ 2^m·(K·D) = (2^m·K)·D ≤ 2^(m+j)·D < 2^(L0+1)
  have hchain : 2 ^ m * distN (a n * b n) (A * B)
      ≤ 2 ^ (m + j) * (distN (a n) A + distN (b n) B) := by
    calc 2 ^ m * distN (a n * b n) (A * B)
        ≤ 2 ^ m * (K * (distN (a n) A + distN (b n) B)) := step1
      _ = (2 ^ m * K) * (distN (a n) A + distN (b n) B) := hassoc
      _ ≤ 2 ^ (m + j) * (distN (a n) A + distN (b n) B) := step2
  exact Nat.lt_of_le_of_lt hchain hcore

/-- **★ `mul_converges_bounded` (∅-axiom, modulus computed).**  The headline:
    instantiate the core's bit-length `j := floorLog 2 K + 1` (so `K < 2^j` by
    `lt_pow_floorLog_succ`).  On `distMet L0`, with `a → A`, `b → B`, and
    uniform bound `K` (`∀ n, a n ≤ K ∧ b n ≤ K`, `B ≤ K`), the product
    `a · b → A · B` with the computed modulus

        m ↦ max (ra (m + (floorLog 2 K + 1) + 1))
                (rb (m + (floorLog 2 K + 1) + 1)). -/
theorem mul_converges_bounded {L0 : Nat} {a b : Nat → Nat} {A B K : Nat}
    {ra rb : Nat → Nat}
    (hbd : ∀ n, a n ≤ K ∧ b n ≤ K) (hBK : B ≤ K)
    (ha : ConvergesWith (distMet L0) a A ra)
    (hb : ConvergesWith (distMet L0) b B rb) :
    ConvergesWith (distMet L0) (fun n => a n * b n) (A * B)
      (fun m => Nat.max (ra (m + (E213.Meta.Nat.FloorLog.floorLog 2 K + 1) + 1))
                        (rb (m + (E213.Meta.Nat.FloorLog.floorLog 2 K + 1) + 1))) :=
  mul_converges_bounded_core
    (Nat.le_of_lt (E213.Meta.Nat.FloorLog.lt_pow_floorLog_succ (by decide)))
    hbd hBK ha hb

/-! ## 5. Non-vacuous: const squeezed by itself -/

/-- `const`-squeezed-`const`: `c = const v` is between `a = b = const v`, both
    `→ v`, so `c → v`.  Instantiates `squeeze_converges` non-vacuously. -/
theorem const_squeeze_converges (L0 v : Nat) :
    ConvergesWith (distMet L0) (fun _ => v) v
      (fun m => Nat.max ((fun _ => 0) (m + 1)) ((fun _ => 0) (m + 1))) :=
  squeeze_converges
    (fun _ => ⟨Nat.le_refl v, Nat.le_refl v⟩)
    (const_converges (distMet L0) v)
    (const_converges (distMet L0) v)

/-- `const · const → product`: two constant sequences `c, d` (bounded by
    `K = Nat.max c d`) multiply to the constant `c * d`.  Instantiates
    `mul_converges_bounded` non-vacuously. -/
theorem const_mul_const_converges (L0 c d : Nat) :
    ConvergesWith (distMet L0) (fun _ => c * d) (c * d)
      (fun m => Nat.max
        ((fun _ => 0) (m + (E213.Meta.Nat.FloorLog.floorLog 2 (Nat.max c d) + 1) + 1))
        ((fun _ => 0) (m + (E213.Meta.Nat.FloorLog.floorLog 2 (Nat.max c d) + 1) + 1))) :=
  mul_converges_bounded
    (fun _ => ⟨E213.Meta.Nat.Max213.le_max_left c d,
               E213.Meta.Nat.Max213.le_max_right c d⟩)
    (E213.Meta.Nat.Max213.le_max_right c d)
    (const_converges (distMet L0) c)
    (const_converges (distMet L0) d)

-- purity probes
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.distN_between
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.squeeze_converges
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.const_squeeze_converges
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.mul_sub_uncond
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.distN_mul_left
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.mul_converges_bounded_core
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.mul_converges_bounded
#print axioms E213.Lib.Math.Analysis.SqueezeProduct.const_mul_const_converges

end E213.Lib.Math.Analysis.SqueezeProduct
