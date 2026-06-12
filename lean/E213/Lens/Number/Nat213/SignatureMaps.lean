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

/-! ## Exhaustiveness — where "nothing else" is proven, and where others provably exist

The natural follow-up: *are these the only maps?*  The answer is
layer-dependent and now made precise.

**Tight layers (iff — nothing else).**

  - **Constant interval ⟺ affine.**  `constInterval_affine` (⟹) and
    `affine_constInterval` (⟸) together say a map has a constant interval
    *iff* it is affine.  No constant-interval map escapes the affine
    normal form.
  - **Additive hom ⟺ `×d`.**  `additiveHom_is_mul` (⟹) and
    `mul_is_additiveHom` (⟸) give `Hom(ℕ,+) = {×d}` exactly.
  - **(Constant interval ∧ first = interval) ⟺ scaling.**
    `firstEqInterval_scaling` (⟹) and `scaling_is_constInterval_firstEq`
    (⟸, below) close layer 3 as an iff.

**The order layer is *not* tight — and provably so.**

At the base, `affine_strictMono` shows affine maps with `d ≥ 1` preserve
order, but the converse is **false**: there are order-embeddings that are
not affine.  `tri_strictMono` + `tri_not_constInterval` exhibit one — the
triangular-number map `tri` is strictly increasing yet has no constant
interval (hence is not affine).  So "그 외가 없다" *fails* at the order
layer; the order-only class is irreducibly infinite, which is the
structural content of order being the weakest signature datum. -/

/-- **Converse of `firstEqInterval_scaling`** (closes layer 3 to an iff):
    the scaling `n ↦ d·(n+1)` has constant interval `d` and first term
    `= d` — i.e. it satisfies the first = interval signature. -/
theorem scaling_is_constInterval_firstEq (d : Nat) :
    (∀ n, d * ((n + 1) + 1) = d * (n + 1) + d) ∧ (d * (0 + 1) = d) := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [Nat.mul_succ]
  · rw [Nat.zero_add, Nat.mul_one]

/-- The triangular-number map `tri n = 0 + 1 + … + n`.  A strictly
    increasing sequence whose forward interval at `n` is `n + 1` — not
    constant.  Witness that the order layer admits non-affine maps. -/
def tri : Nat → Nat
  | 0     => 0
  | n + 1 => tri n + (n + 1)

/-- One step of `tri` strictly increases (interval `n + 1 ≥ 1 > 0`). -/
theorem tri_step_lt (n : Nat) : tri n < tri (n + 1) :=
  Nat.lt_add_of_pos_right (Nat.succ_pos n)

/-- A map increasing at every step is strictly monotone — the
    order-embedding criterion, stated in the `m + (j+1)` form. -/
private theorem strictMono_of_step (g : Nat → Nat)
    (hstep : ∀ k, g k < g (k + 1)) : ∀ m j, g m < g (m + (j + 1)) := by
  intro m j
  induction j with
  | zero => exact hstep m
  | succ i ih =>
      have hnext : g (m + (i + 1)) < g (m + (i + 1 + 1)) := by
        have hs := hstep (m + (i + 1))
        rwa [Nat.add_assoc m (i + 1) 1] at hs
      exact Nat.lt_trans ih hnext

/-- **`tri` preserves order** (is a strict order-embedding). -/
theorem tri_strictMono {m n : Nat} (h : m < n) : tri m < tri n := by
  have hpos : n - m ≠ 0 :=
    fun he => Nat.lt_irrefl 0 (he ▸ E213.Tactic.NatHelper.sub_pos_of_lt h)
  have hj : m + ((n - m - 1) + 1) = n := by
    rw [E213.Tactic.NatHelper.sub_one_add_one hpos,
        E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt h)]
  have key := strictMono_of_step tri tri_step_lt m (n - m - 1)
  rwa [hj] at key

/-- **`tri` has no constant interval** — hence is not affine, yet (by
    `tri_strictMono`) preserves order.  This proves the order-only class
    contains maps *outside* the affine family: "그 외가 있다". -/
theorem tri_not_constInterval : ¬ ∃ d, ∀ n, tri (n + 1) = tri n + d := by
  intro h
  obtain ⟨d, hd⟩ := h
  -- step 0: tri 1 = tri 0 + 1, and = tri 0 + d  ⟹  d = 1
  have e0 : tri 0 + 1 = tri 0 + d := hd 0
  have hd1 : d = 1 := (E213.Tactic.NatHelper.add_left_cancel e0).symm
  -- step 1: tri 2 = tri 1 + 2, and = tri 1 + d = tri 1 + 1  ⟹  2 = 1
  have e1 : tri 1 + 2 = tri 1 + d := hd 1
  rw [hd1] at e1
  have h21 : (2 : Nat) = 1 := E213.Tactic.NatHelper.add_left_cancel e1
  exact Nat.noConfusion (Nat.succ.inj h21)

/-! ## Full rigidity — every order-automorphism of ℕ is the identity

`affine_surj_id` proved rigidity *within* the affine family.  Here it is
proved over **arbitrary** maps: a strictly monotone surjection (an
order-automorphism of `(ℕ, ≤)`) is forced to be the identity.  Two
ingredients: a strictly monotone map dominates its index (`strictMono_ge`,
`n ≤ f n`), and strict monotonicity is monotone (`strictMono_mono`).  The
apex of the tower with no affine assumption: `Aut(ℕ⁺, ≤) = {id}`. -/

/-- A strictly monotone `f : ℕ → ℕ` dominates the index: `n ≤ f n`. -/
theorem strictMono_ge (f : Nat → Nat) (hmono : ∀ {a b}, a < b → f a < f b) :
    ∀ n, n ≤ f n := by
  intro n
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih (hmono (Nat.lt_succ_self k)))

/-- Strict monotonicity is monotonicity: `a ≤ b → f a ≤ f b`. -/
theorem strictMono_mono (f : Nat → Nat)
    (hmono : ∀ {a b}, a < b → f a < f b) {a b : Nat} (h : a ≤ b) :
    f a ≤ f b := by
  rcases Nat.eq_or_lt_of_le h with he | hl
  · exact Nat.le_of_eq (congrArg f he)
  · exact Nat.le_of_lt (hmono hl)

/-- **Full order rigidity.**  A strictly monotone surjection of ℕ — an
    order-automorphism of `(ℕ, ≤)` — is the identity.  No affine
    hypothesis: `Aut(ℕ⁺, ≤) = {id}`. -/
theorem orderAuto_id (f : Nat → Nat)
    (hmono : ∀ {a b}, a < b → f a < f b)
    (hsurj : ∀ y, ∃ x, f x = y) : ∀ n, f n = n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hge : n ≤ f n := strictMono_ge f hmono n
      obtain ⟨k, hk⟩ := hsurj n
      rcases Nat.lt_or_ge k n with hlt | hge2
      · -- k < n: by IH f k = k, but f k = n ⟹ k = n, contradiction
        have hkn : k = n := (ih k hlt).symm.trans hk
        exact absurd (hkn ▸ hlt) (Nat.lt_irrefl n)
      · -- n ≤ k ⟹ f n ≤ f k = n; with n ≤ f n ⟹ f n = n
        have hle : f n ≤ f k := strictMono_mono f hmono hge2
        rw [hk] at hle
        exact Nat.le_antisymm hle hge

/-! ## Classification of the order layer — the gap / partial-sum normal form

What form does an order-preserving map take?  Just as a *constant*
interval reconstructs an affine map (`constInterval_affine`), an
*arbitrary* gap sequence reconstructs a monotone map.  Every monotone
`f` is its first value plus the running sum of its forward gaps
(`monotone_eq_first_add_psum_gap`):

```
f n = f 0 + Σ_{i<n} (f(i+1) − f i).
```

So the order-only class is parameterised by `(f 0, gap f)` — a starting
value and a whole **gap sequence** `gap f : ℕ → ℕ`.  The sub-classes are
cut by the gap sequence:

  - **gap constant `≡ d`** → affine `n ↦ f 0 + d·n` (`affine_gap`
    computes `gap (affine a d) = d`; the converse is `constInterval_affine`);
  - **gap pointwise `≥ 1`** → strictly monotone / order-embedding
    (`gap_pos_of_step`; converse via `strictMono_of_step`);
  - **gap pointwise `≥ 0`** → weakly monotone (non-decreasing).

This is the precise sense of "infinite-dimensional" at the base: the
affine layer fixes the gap to a single number, the order layer lets it be
an arbitrary sequence.  (Equivalently, an order-embedding ↔ its image, an
infinite subset of ℕ enumerated increasingly — the same data as a
pointwise-`≥1` gap sequence with a starting value.) -/

/-- The forward gap of a map at `n`. -/
def gap (f : Nat → Nat) (n : Nat) : Nat := f (n + 1) - f n

/-- The running (partial) sum of a gap sequence. -/
def psum (g : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => psum g n + g n

/-- **Order-layer normal form.**  Every monotone map is its first value
    plus the partial sum of its gaps: `f n = f 0 + Σ_{i<n} gap f i`.  The
    sequence-parameterised analogue of `constInterval_affine`. -/
theorem monotone_eq_first_add_psum_gap (f : Nat → Nat)
    (hmono : ∀ n, f n ≤ f (n + 1)) :
    ∀ n, f n = f 0 + psum (gap f) n := by
  intro n
  induction n with
  | zero =>
      show f 0 = f 0 + 0
      rw [Nat.add_zero]
  | succ k ih =>
      have hstep : f (k + 1) = f k + gap f k := by
        show f (k + 1) = f k + (f (k + 1) - f k)
        rw [E213.Tactic.NatHelper.add_sub_of_le (hmono k)]
      show f (k + 1) = f 0 + (psum (gap f) k + gap f k)
      rw [hstep, ih, Nat.add_assoc]

/-- **Affine ⟺ constant gap.**  An affine map has constant gap `d`
    (recovering the affine slice of the normal form; converse is
    `constInterval_affine`). -/
theorem affine_gap (a d n : Nat) : gap (affine a d) n = d := by
  show (a + d * (n + 1)) - (a + d * n) = d
  rw [Nat.mul_succ, ← Nat.add_assoc, Nat.add_comm (a + d * n) d]
  exact E213.Tactic.NatHelper.add_sub_cancel_right d (a + d * n)

/-- **Strictly monotone ⟹ gaps `≥ 1`.**  An order-embedding has positive
    gaps everywhere (converse: positive gaps give `strictMono_of_step`). -/
theorem gap_pos_of_step (f : Nat → Nat) (n : Nat) (h : f n < f (n + 1)) :
    1 ≤ gap f n :=
  E213.Tactic.NatHelper.sub_pos_of_lt h

/-! ## Weakly monotone — the staircase (repeats allowed)

A non-decreasing map is a *staircase*: where its gap is `0` it repeats the
previous value (a plateau), where the gap is `≥ 1` it steps strictly up.
The two characterizations below cleanly split the strict from the weak:
gap `= 0` ⟺ a repeat, gap `≥ 1` ⟺ a strict step.  So a weakly monotone
map is strictly monotone *exactly* when it has no plateaus (no zero gap),
and a genuine staircase otherwise. -/

/-- **Plateau ⟺ zero gap.**  For a non-decreasing map, a repeated value is
    exactly a zero gap. -/
theorem gap_zero_iff_repeat (f : Nat → Nat) (hmono : ∀ n, f n ≤ f (n + 1))
    (n : Nat) : gap f n = 0 ↔ f (n + 1) = f n := by
  constructor
  · intro hg
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hg) (hmono n)
  · intro he
    show f (n + 1) - f n = 0
    rw [he, Nat.sub_self]

/-- **Strict step ⟺ positive gap.**  For a non-decreasing map, a strict
    increase at `n` is exactly a gap `≥ 1`. -/
theorem step_iff_gap_pos (f : Nat → Nat) (hmono : ∀ n, f n ≤ f (n + 1))
    (n : Nat) : f n < f (n + 1) ↔ 1 ≤ gap f n := by
  constructor
  · exact gap_pos_of_step f n
  · intro hpos
    have he : f n + gap f n = f (n + 1) :=
      E213.Tactic.NatHelper.add_sub_of_le (hmono n)
    have hlt : f n < f n + gap f n := Nat.lt_add_of_pos_right hpos
    rwa [he] at hlt

/-! ## Order-embedding ⟹ infinite subset of ℕ (image side only)

An order-embedding maps onto an **infinite subset of ℕ**.  This direction
is proved: the embedding is injective (`strictMono_injective` — a faithful
enumeration, hits each image point once) and its image is unbounded
(`strictMono_unbounded` — meets every threshold, since `N ≤ f N`).
Injective + unbounded = the image is an infinite subset.

The **reverse** direction — every infinite subset of ℕ arises as the image
of a unique increasing enumeration, making this a bijection (↔) — is
**not** formalized here.  It needs an enumerator built by bounded search
("least `n ≥ k` in the subset") with termination from unboundedness;
recorded as open, not claimed. -/

/-- A strictly monotone map is injective (faithful enumeration). -/
theorem strictMono_injective (f : Nat → Nat)
    (hmono : ∀ {a b}, a < b → f a < f b) {a b : Nat} (h : f a = f b) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hl | he | hg
  · exact absurd h (Nat.ne_of_lt (hmono hl))
  · exact he
  · exact absurd h.symm (Nat.ne_of_lt (hmono hg))

/-- The image of a strictly monotone map is unbounded — meets every
    threshold `N` (since `N ≤ f N`).  Hence the image is infinite. -/
theorem strictMono_unbounded (f : Nat → Nat)
    (hmono : ∀ {a b}, a < b → f a < f b) (N : Nat) : ∃ n, N ≤ f n :=
  ⟨N, strictMono_ge f hmono N⟩

/-! ## ℕ⁺ on the Raw readout — the tower anchored where `0` cannot occur

The theorems above run over Lean `Nat = {0, 1, 2, …}` as the *underlying
arithmetic*.  But ℕ⁺ is the **Raw readout**: `Raw.value : Raw → Nat` lands
in `{1, 2, 3, …}` (`value_pos : 1 ≤ Raw.value r`), and hits every positive
value (`Raw.value_numeral_pred`).  So ℕ⁺ is exactly the image of the
readout — `natPlus_iff_value` — and `0` structurally cannot occur.  This
section re-anchors the signature tower there, so positivity is carried by
the residue, not assumed:

  - canonical ℕ⁺ object `1, 2, 3, …` = the readout of the atom chart
    (`canonical_natPlus`);
  - **order** — the readout is strictly increasing
    (`chartChain_readout_strictMono`, interval `value r' ≥ 1`);
  - **constant interval ⟹ affine** on the readout (`chartChain_is_affine`,
    above; `value r₀`, `value r'` both `≥ 1`);
  - **first = interval ⟹ scaling** on the readout
    (`chartChain_firstEqInterval`, above);
  - **rigidity** — the *only* strictly increasing enumeration of ℕ⁺
    (starting at the floor `1`, onto all of ℕ⁺) is `n ↦ n + 1`
    (`natPlus_enum_unique`); proved by shifting to `orderAuto_id` at the
    ℕ⁺ floor instead of `0`. -/

/-- **ℕ⁺ = the readout image.**  A value is positive iff it is some Raw's
    `value`.  `⟸` is `value_pos`; `⟹` is the numeral section
    `value_numeral_pred`.  So the readout codomain is exactly ℕ⁺. -/
theorem natPlus_iff_value (v : Nat) : 1 ≤ v ↔ ∃ r : Raw, Raw.value r = v := by
  constructor
  · intro hv; exact ⟨Raw.numeral (v - 1), Raw.value_numeral_pred v hv⟩
  · rintro ⟨r, hr⟩; rw [← hr]; exact value_pos r

/-- **Canonical ℕ⁺ object.**  The atom chart `(a, b)` reads out as
    `1, 2, 3, …` — first term `1`, interval `1`, the first = interval
    coincidence at the floor. -/
theorem canonical_natPlus (h : Raw.a ≠ Raw.b) (n : Nat) :
    Raw.value (chartChain Raw.a Raw.b h n) = n + 1 := by
  rw [chartChain_value, Raw.value_a, Raw.value_b, Nat.mul_one, Nat.add_comm]

/-- **Order on the readout.**  Every chart's ℕ⁺ readout is strictly
    increasing (its interval `value r' ≥ 1` by `value_pos`). -/
theorem chartChain_readout_strictMono (r₀ r' : Raw) (h : r₀ ≠ r')
    {m n : Nat} (hmn : m < n) :
    Raw.value (chartChain r₀ r' h m) < Raw.value (chartChain r₀ r' h n) := by
  rw [chartChain_is_affine, chartChain_is_affine]
  exact affine_strictMono (Raw.value r₀) (Raw.value r') (value_pos r') hmn

/-- **ℕ⁺ rigidity.**  A strictly increasing map starting at the ℕ⁺ floor
    (`1 ≤ g 0`) and surjecting onto ℕ⁺ (`∀ v ≥ 1, ∃ n, g n = v`) is the
    canonical enumeration `n ↦ n + 1`.  The genuine ℕ⁺ apex: the only
    increasing enumeration of ℕ⁺ is `1, 2, 3, …`.  Proved by shifting
    `g − 1` to `orderAuto_id` (floor `1`, not `0`). -/
theorem natPlus_enum_unique (g : Nat → Nat)
    (hmono : ∀ {a b}, a < b → g a < g b) (hstart : 1 ≤ g 0)
    (hsurj : ∀ v, 1 ≤ v → ∃ n, g n = v) : ∀ n, g n = n + 1 := by
  have hpos : ∀ n, 1 ≤ g n := fun n =>
    Nat.le_trans hstart (strictMono_mono g hmono (Nat.zero_le n))
  have hmono_f : ∀ {a b}, a < b → g a - 1 < g b - 1 := by
    intro a b hab
    exact E213.Tactic.NatHelper.sub_lt_sub_right 1 (hpos a) (hmono hab)
  have hsurj_f : ∀ y, ∃ n, g n - 1 = y := by
    intro y
    obtain ⟨n, hn⟩ := hsurj (y + 1) (Nat.succ_le_succ (Nat.zero_le y))
    exact ⟨n, by rw [hn]; exact E213.Tactic.NatHelper.add_sub_cancel_right y 1⟩
  intro n
  have hfn : g n - 1 = n := orderAuto_id (fun m => g m - 1) hmono_f hsurj_f n
  have hne : g n ≠ 0 := by
    intro he
    have h10 : (1 : Nat) ≤ 0 := he ▸ hpos n
    exact Nat.not_succ_le_zero 0 h10
  have hstep : g n - 1 + 1 = n + 1 := congrArg (· + 1) hfn
  rwa [E213.Tactic.NatHelper.sub_one_add_one hne] at hstep

end E213.Lens.Number.Nat213
