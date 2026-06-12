import E213.Lens.Number.Nat213.ChartGeneral
import E213.Meta.Tactic.NatHelper

/-!
# Lens.Number.Nat213.SignatureMaps — the morphism tower of ℕ⁺'s signature

ℕ⁺ arrives, under the count-Lens, as the chain whose readout is an
arithmetic progression.  `ChartGeneral.chartChain_value` already records
the general form

```
value (chartChain r₀ r' h n) = value r₀ + n · value r'
```

i.e. **first term `value r₀`, interval `value r'`**.  ℕ⁺'s signature is
exactly the three data of this readout:

  1. **순서 / order** — the chain is strictly increasing (`<`);
  2. **일정한 간격 / constant interval** — the forward difference is a
     single constant `d`;
  3. **초항 = 간격 / first = interval** — the seed value equals the step.

A *map* `φ : Nat → Nat` (position ↦ value) is classified by **how many
of the three it preserves**.  This file proves that the answer is a
nested tower, each clause cutting the previous class by one degree of
freedom:

| preserved | morphism class | normal form | params |
|---|---|---|---|
| order only | order-embedding (strictly monotone) | any `<`-increasing seq | ∞ |
| + constant interval | affine map (= the general chart) | `n ↦ a + d·n` | 2 |
| + first = interval | scaling / multiplicative map | `n ↦ d·(n+1)` | 1 |
| all three (d = 1) | identity (rigidity) | `n ↦ n` | 0 |

The theorems below establish each transition rigorously:

  - `constInterval_affine` — constant interval ⟹ affine (telescoping);
  - `affine_strictMono` — `d ≥ 1` ⟹ strictly monotone (order is the
    weakest layer, automatic once the interval is positive);
  - `firstEqInterval_scaling` — first = interval ⟹ pure scaling
    `n ↦ d·(n+1)` of the canonical `1,2,3,…`;
  - `additiveHom_is_mul` / `mul_is_additiveHom` — the multiplicative
    collapse: the additive endomorphisms of `(ℕ,+)` are **exactly** the
    `×d` maps (the `a = 0` diagonal of the affine monoid);
  - `affine_comp` — the affine composition (chart-monoid) law
    `(a,d)∘(a',d') = (a + d·a', d·d')`;
  - `scaling_comp` / `affine_id` — the scalings form a submonoid with
    `×1` as unit (the `(ℕ,·)` multiplicative monoid realised as maps);
  - `affine_surj_id` — rigidity: a *surjective* affine self-map of ℕ is
    forced to be the identity (`a = 0 ∧ d = 1`).

Raw-level anchors tying the tower back to the residue:

  - `chartChain_is_affine` — the general chart **is** the affine map,
    with `a = value r₀` (초항) and `d = value r'` (간격);
  - `chartChain_firstEqInterval` — when seed-value = step-value, the
    chart collapses to the scaling `n ↦ value r' · (n+1)`.

∅-axiom standard; no Mathlib, no Classical, no propext / Quot.sound,
no omega, no kernel decision procedure.
-/

namespace E213.Lens.Number.Nat213

open E213.Theory E213.Theory.Raw.Endomorphic

/-! ## The affine normal form -/

/-- An affine map on positions: first term `a`, interval `d`.
    `affine a d n = a + d·n`.  This is the value-readout normal form of
    a constant-interval chain (proved below) and the general chart of
    `ChartGeneral` (`chartChain_is_affine`). -/
def affine (a d n : Nat) : Nat := a + d * n

/-! ## Layer 2 — constant interval ⟹ affine (telescoping)

The defining property of ℕ⁺'s signature is a *single* forward
difference `d`.  Telescoping that constant difference reconstructs the
whole map as affine.  This is the precise sense in which "일정한 간격"
generates the 2-parameter chart family. -/

/-- **Constant interval ⟹ affine.**  If `φ` has constant forward
    difference `d`, then `φ n = φ 0 + n·d`.  Pure induction (telescope). -/
theorem constInterval_affine (φ : Nat → Nat) (d : Nat)
    (h : ∀ n, φ (n + 1) = φ n + d) : ∀ n, φ n = φ 0 + n * d := by
  intro n
  induction n with
  | zero =>
      show φ 0 = φ 0 + 0 * d
      rw [Nat.zero_mul, Nat.add_zero]
  | succ k ih =>
      rw [h k, ih, Nat.succ_mul, Nat.add_assoc]

/-- The affine map *is* a constant-interval map with difference `d`.
    Converse of `constInterval_affine`. -/
theorem affine_constInterval (a d : Nat) :
    ∀ n, affine a d (n + 1) = affine a d n + d := by
  intro n
  show a + d * (n + 1) = (a + d * n) + d
  rw [Nat.mul_succ, ← Nat.add_assoc]

/-! ## Order layer — `d ≥ 1` ⟹ strictly monotone

Order is the *weakest* of the three: any constant-interval map with a
positive step is already an order-embedding.  So "순서" sits at the base
of the tower, automatically satisfied the moment the interval is a
genuine distinguishing (`d ≥ 1`). -/

/-- **Positive interval ⟹ strictly monotone (order-embedding).**  An
    affine map with `d ≥ 1` strictly increases. -/
theorem affine_strictMono (a d : Nat) (hd : 1 ≤ d) {m n : Nat}
    (hmn : m < n) : affine a d m < affine a d n := by
  show a + d * m < a + d * n
  apply Nat.add_lt_add_left
  have hdpos : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_one hd
  have hpos : 0 < d * (n - m) :=
    Nat.mul_pos hdpos (E213.Tactic.NatHelper.sub_pos_of_lt hmn)
  have hsplit : d * m + d * (n - m) = d * n := by
    rw [← Nat.mul_add, E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hmn)]
  rw [← hsplit]
  exact Nat.lt_add_of_pos_right hpos

/-! ## Layer 3a — first = interval ⟹ scaling

The third signature datum, `φ 0 = d` (first term = interval), is the
diagonal `a = d` of the affine family.  Imposing it collapses the
2-parameter affine map to the 1-parameter pure scaling
`n ↦ d·(n+1)` — `d` copies of the canonical chain `1, 2, 3, …`. -/

/-- **First = interval ⟹ scaling.**  A constant-interval map whose first
    term equals its interval `d` is the pure scaling `n ↦ d·(n+1)` —
    `d` times the canonical ℕ⁺ chain.  This is the "곱 사상" the signature
    licenses. -/
theorem firstEqInterval_scaling (φ : Nat → Nat) (d : Nat)
    (hint : ∀ n, φ (n + 1) = φ n + d) (hfirst : φ 0 = d) :
    ∀ n, φ n = d * (n + 1) := by
  intro n
  rw [constInterval_affine φ d hint n, hfirst, Nat.mul_succ,
      Nat.mul_comm d n, Nat.add_comm]

/-! ## Layer 3b — the multiplicative collapse

The scalings are not just *a* class — they are exactly the additive
endomorphisms of `(ℕ,+)`.  A map respects the additive structure the
interval generates iff it is `×d`.  This pins "first = interval" as the
clause that turns the additive chart into the multiplicative monoid. -/

/-- **Additive homomorphisms of `(ℕ,+)` are exactly `×d`.**  If
    `f (m + n) = f m + f n`, then `f n = f 1 · n`.  (One direction of the
    multiplicative collapse.) -/
theorem additiveHom_is_mul (f : Nat → Nat)
    (h : ∀ m n, f (m + n) = f m + f n) : ∀ n, f n = f 1 * n := by
  have h0 : f 0 = 0 := by
    have e : f 0 = f 0 + f 0 := by
      have := h 0 0
      rwa [Nat.add_zero] at this
    have e' : f 0 + 0 = f 0 + f 0 := by rw [Nat.add_zero]; exact e
    exact (E213.Tactic.NatHelper.add_left_cancel e').symm
  intro n
  induction n with
  | zero => rw [h0, Nat.mul_zero]
  | succ k ih =>
      rw [h k 1, ih, Nat.mul_succ]

/-- Converse: `×d` is an additive homomorphism.  Together with
    `additiveHom_is_mul`, `Hom(ℕ,+) = { ×d : d ∈ ℕ }`. -/
theorem mul_is_additiveHom (d : Nat) :
    ∀ m n, d * (m + n) = d * m + d * n := fun m n => Nat.mul_add d m n

/-! ## Layer 4 — composition, the chart monoid, and rigidity -/

/-- **Affine composition law** (the chart monoid):
    `(a,d) ∘ (a',d') = (a + d·a', d·d')`.  The first components shift,
    the intervals multiply — the affine monoid `ℕ ⋊ ℕ`. -/
theorem affine_comp (a d a' d' n : Nat) :
    affine a d (affine a' d' n) = affine (a + d * a') (d * d') n := by
  show a + d * (a' + d' * n) = (a + d * a') + (d * d') * n
  rw [Nat.mul_add, E213.Meta.Nat.PureNat.mul_assoc, Nat.add_assoc]

/-- `×1` (the canonical chart) is the identity map. -/
theorem affine_id (n : Nat) : affine 0 1 n = n := by
  show 0 + 1 * n = n
  rw [Nat.one_mul, Nat.zero_add]

/-- **The scalings form a submonoid.**  The `a = 0` diagonal is closed
    under composition with intervals multiplying:
    `(×d) ∘ (×d') = ×(d·d')`.  With `affine_id` as unit, this realises the
    multiplicative monoid `(ℕ,·)` as maps — the morphism shadow of
    "first = interval". -/
theorem scaling_comp (d d' n : Nat) :
    affine 0 d (affine 0 d' n) = affine 0 (d * d') n := by
  rw [affine_comp]
  show affine (0 + d * 0) (d * d') n = affine 0 (d * d') n
  rw [Nat.mul_zero, Nat.add_zero]

/-! ### Rigidity — all three pinned ⟹ identity

A surjective affine self-map of ℕ is forced to the identity: hitting `0`
forces `a = 0`, then hitting `1` forces `d = 1`.  This is the apex of the
tower — fixing order + interval + (first = interval, with the canonical
value `1`) leaves no freedom, the well-order rigidity of ℕ⁺. -/

/-- `n + 1 ≠ 0` (∅-axiom; core `Nat.succ_ne_zero` carries propext). -/
private theorem succ_ne_zero' {n : Nat} : n + 1 ≠ 0 :=
  fun h => Nat.noConfusion h

/-- `a + b = 0 → a = 0 ∧ b = 0` (∅-axiom, direct recursion). -/
private theorem add_eq_zero : ∀ {a b : Nat}, a + b = 0 → a = 0 ∧ b = 0
  | 0, 0, _ => ⟨rfl, rfl⟩
  | 0, _ + 1, h => absurd h succ_ne_zero'
  | _ + 1, b, h => absurd (Nat.succ_add _ b ▸ h) succ_ne_zero'

/-- `a * b = 1 → a = 1 ∧ b = 1` (∅-axiom, term-mode case match). -/
private theorem mul_eq_one : ∀ {a b : Nat}, a * b = 1 → a = 1 ∧ b = 1
  | 0, b, h =>
      Nat.noConfusion ((Nat.zero_mul b).symm.trans h)
  | a + 1, 0, h =>
      Nat.noConfusion ((Nat.mul_zero (a + 1)).symm.trans h)
  | a + 1, b + 1, h => by
      -- (a+1)*(b+1) = (a*b + a + b) + 1 = 1  ⟹  a*b + a + b = 0  ⟹  a = b = 0
      have expand : (a + 1) * (b + 1) = (a * b + a + b) + 1 := by
        rw [Nat.succ_mul, Nat.mul_succ, ← Nat.add_assoc]
      rw [expand] at h
      have hz : a * b + a + b = 0 := Nat.succ.inj h
      have h2 := (add_eq_zero hz).2
      have h1 := (add_eq_zero (add_eq_zero hz).1).2
      rw [h1, h2]
      exact ⟨rfl, rfl⟩

/-- **Rigidity.**  A *surjective* affine self-map of ℕ has `a = 0` and
    `d = 1` — hence is the identity (`affine_id`).  Pinning all three
    signature data leaves only the identity: `Aut(ℕ⁺, succ, ≤) = {id}`. -/
theorem affine_surj_id (a d : Nat)
    (hsurj : ∀ y, ∃ n, affine a d n = y) : a = 0 ∧ d = 1 := by
  obtain ⟨n0, hn0⟩ := hsurj 0
  -- affine a d n0 = a + d*n0 = 0  ⟹  a = 0
  have ha : a = 0 := (add_eq_zero hn0).1
  obtain ⟨n1, hn1⟩ := hsurj 1
  -- affine a d n1 = a + d*n1 = 1, with a = 0  ⟹  d*n1 = 1  ⟹  d = 1
  have hd1 : d * n1 = 1 := by
    have hz : (0 : Nat) + d * n1 = 1 := by rw [← ha]; exact hn1
    rwa [Nat.zero_add] at hz
  exact ⟨ha, (mul_eq_one hd1).1⟩

/-! ## Raw-level anchors — the tower lives on the residue

These tie the abstract morphism classes back to `chartChain`: the
general chart **is** the affine map, and the first = interval coincidence
**is** the scaling collapse, at the level of the Raw readout. -/

/-- **The general chart is the affine map.**  `value r₀` is the first
    term (초항), `value r'` the interval (간격). -/
theorem chartChain_is_affine (r₀ r' : Raw) (h : r₀ ≠ r') (n : Nat) :
    Raw.value (chartChain r₀ r' h n)
      = affine (Raw.value r₀) (Raw.value r') n := by
  rw [chartChain_value]
  show Raw.value r₀ + n * Raw.value r' = Raw.value r₀ + Raw.value r' * n
  rw [Nat.mul_comm]

/-- **First = interval ⟹ scaling, on the residue.**  When seed-value
    equals step-value, the chart collapses to the pure scaling
    `n ↦ value r' · (n+1)` — `value r'` copies of the canonical chain. -/
theorem chartChain_firstEqInterval (r₀ r' : Raw) (h : r₀ ≠ r')
    (hval : Raw.value r₀ = Raw.value r') (n : Nat) :
    Raw.value (chartChain r₀ r' h n) = Raw.value r' * (n + 1) := by
  rw [chartChain_value, hval, Nat.mul_succ, Nat.mul_comm (Raw.value r') n,
      Nat.add_comm]

end E213.Lens.Number.Nat213
