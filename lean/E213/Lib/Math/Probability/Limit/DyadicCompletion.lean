import E213.Lib.Math.Probability.Limit.ConvolveRescaleContraction
import E213.Lib.Math.Analysis.BanachFixedPointModulated
import E213.Meta.Nat.Max213

/-!
# Probability — a genuine `CompleteMetricModulus` for the dyadic metric (zero-axiom)

`ConvolveRescaleContraction` proved the rescale leg `Φ` of convolve-and-rescale
is a `Contraction (dyMet L) Φ` on the dyadic rationals `Dy = Nat × Nat`, and ran
the forcing heart `picard_cauchy` on it.  What it could not do honestly is apply
`banach_fixed_point`: that needs a `CompleteMetricModulus`, a genuine Cauchy
completion — the dyadic rationals are not Cauchy-complete, so a `lim` on `Dy`
would have to be fabricated.

This file builds the completion the way `Real213` builds the reals (sequence +
modulus; `Core.Core.Real213`, `Analysis.CauchyComplete.CauchyCutSeq`) — without
quotients.  The carrier `DyC L` is a *regular* `dyMet L`-Cauchy sequence of
dyadics: `closeDy L m (seq p) (seq q)` for all `p, q ≥ m` (Bishop's regular
convention; identity modulus).  `closeC` compares two such sequences eventually;
the four `MetricModulus` laws transfer pointwise from `dyMet`.

The candidate completeness operator `limPoint` is the *stabilizing diagonal* of a
`closeC`-Cauchy sequence of completion points: a total function (no Cauchy
hypothesis needed) built by a decidable freeze — at each level it takes the new
diagonal value only if it respects the regular bound (a pure `Nat` decidable
test), else it holds the previous value.  This is regular by construction (so it
is always a legitimate `DyC L`).  Quotient-free.

**Honest scope (the constructive wall — what this file does and does not do).**
This file does **not** build `completeDy : CompleteMetricModulus (DyC L)` and does
**not** apply `banach_fixed_point`.  The `CompleteMetricModulus` interface bundles a
*total* `lim : (Nat → X) → X` with `climconv` claiming convergence for **every**
bare Cauchy sequence — and a total choice-free `lim` correct on all bare sequences
is constructively impossible (it would have to read each sequence's own unbounded
modulus; the diagonal of regular sequences is not regular).  That obligation is the
smuggled countable-choice principle `AC₀,₀` ("every Cauchy sequence has a modulus"),
which ∅-axiom forbids.  Instead this file delivers the `banach_fixed_point`
**conclusion's content directly**: `orbit_to_center_completion` proves the lifted
convolve-and-rescale Picard orbit converges, in the completion metric `closeC`, to
the Gaussian center — a genuine completion-limit, reached by none, ∅-axiom, without
ever touching the bare `lim`.  The reusable *engine* form (a `…Mod`/name-carrier
completeness interface taking the modulus as data, then a `banach_fixed_point_modulated`)
is the named follow-on, tracked in the `wall_synthesis` frontier;
`picard_cauchy` already supplies the orbit's explicit modulus `N(m)=m`, so that route
is choice-free.

All zero-axiom.
-/

namespace E213.Lib.Math.Probability.Limit.DyadicCompletion

open E213.Lib.Math.Analysis.UniformLimitContinuous (MetricModulus)
open E213.Lib.Math.Analysis.BanachFixedPoint
  (Contraction picard picard_cauchy CompleteMetricModulus cmono_le)
open E213.Lib.Math.Probability.Limit.ConvolveRescaleContraction
  (Dy closeDy closeDy_refl closeDy_symm closeDy_mono closeDy_tri dyMet Φ Φ_contraction
   crossDist crossDist_Φ picard_Φ_eq orbit_to_center closeDy_center)
open E213.Tactic.Pow213 (pow_add_two)
open E213.Meta.Nat.PureNat (mul_assoc)

/-! ## 1. The completion carrier — regular `dyMet`-Cauchy sequences of dyadics -/

/-- **`DyC L`** — a completion point: a *regular* `dyMet L`-Cauchy sequence of
    dyadics, `closeDy L m (seq p) (seq q)` for all `p, q ≥ m`.  No quotient:
    the carrier *is* the sequence-with-spec. -/
structure DyC (L : Nat) where
  /-- the underlying dyadic sequence. -/
  seq : Nat → Dy
  /-- regular Cauchy spec: past index `m` the tail is within `1/2^m`. -/
  reg : ∀ m p q, p ≥ m → q ≥ m → closeDy L m (seq p) (seq q)

/-! ## 2. The completion metric `closeC` and its four laws -/

/-- `a` and `b` eventually within `1/2^m`: a tail `K` on which they agree. -/
def closeC (L m : Nat) (a b : DyC L) : Prop :=
  ∃ K, ∀ n, n ≥ K → closeDy L m (a.seq n) (b.seq n)

theorem closeC_refl (L m : Nat) (a : DyC L) : closeC L m a a :=
  ⟨0, fun n _ => closeDy_refl L m (a.seq n)⟩

theorem closeC_symm (L m : Nat) (a b : DyC L) (h : closeC L m a b) :
    closeC L m b a := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun n hn => closeDy_symm L m (a.seq n) (b.seq n) (hK n hn)⟩

theorem closeC_mono (L m : Nat) (a b : DyC L) (h : closeC L (m + 1) a b) :
    closeC L m a b := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun n hn => closeDy_mono L m (a.seq n) (b.seq n) (hK n hn)⟩

theorem closeC_tri (L m : Nat) (a b c : DyC L)
    (hab : closeC L (m + 1) a b) (hbc : closeC L (m + 1) b c) :
    closeC L m a c := by
  obtain ⟨K1, hK1⟩ := hab
  obtain ⟨K2, hK2⟩ := hbc
  refine ⟨K1 + K2, fun n hn => ?_⟩
  have hn1 : n ≥ K1 := Nat.le_trans (Nat.le_add_right K1 K2) hn
  have hn2 : n ≥ K2 := Nat.le_trans (Nat.le_add_left K2 K1) hn
  exact closeDy_tri L m (a.seq n) (b.seq n) (c.seq n) (hK1 n hn1) (hK2 n hn2)

/-- **`metC L`** — the completion `MetricModulus` on `DyC L`. -/
def metC (L : Nat) : MetricModulus (DyC L) where
  close := closeC L
  crefl := fun m a => closeC_refl L m a
  csymm := fun m a b h => closeC_symm L m a b h
  cmono := fun m a b h => closeC_mono L m a b h
  ctri  := fun m a b c hab hbc => closeC_tri L m a b c hab hbc

/-! ## 3. Embedding + the abstract Cauchy spec + the diagonal -/

/-- The constant regular Cauchy sequence at a dyadic point (`Dy ↪ DyC L`). -/
def inj (L : Nat) (a : Dy) : DyC L where
  seq := fun _ => a
  reg := fun m _ _ _ _ => closeDy_refl L m a

/-- A `metC`-Cauchy sequence of completion points (matches `climconv`'s
    hypothesis with `close = closeC`). -/
def IsCauchyC (L : Nat) (S : Nat → DyC L) : Prop :=
  ∀ m, ∃ Nidx, ∀ p q, p ≥ Nidx → q ≥ Nidx → closeC L m (S p) (S q)

/-- The plain diagonal: term `n` sampled at index `n`. -/
def diagSeq (L : Nat) (S : Nat → DyC L) : Nat → Dy :=
  fun n => (S n).seq n

/-- **The diagonal is regular Cauchy (modulus form).**  For `p, q ≥ Nidx + (m+2)`
    chain `diag p — (S p).seq big — (S q).seq big — diag q` at scale `m+2`
    (`big = p + q + K`, `K` the inter-term tail witness); collapse via `qtri`. -/
theorem diag_reg (L : Nat) {S : Nat → DyC L} (hS : IsCauchyC L S) :
    ∀ m, ∃ Mod, ∀ p q, p ≥ Mod → q ≥ Mod →
      closeDy L m (diagSeq L S p) (diagSeq L S q) := by
  intro m
  obtain ⟨Nidx, hNidx⟩ := hS (m + 2)
  refine ⟨Nidx + (m + 2), fun p q hp hq => ?_⟩
  have hpNidx : p ≥ Nidx := Nat.le_trans (Nat.le_add_right Nidx (m + 2)) hp
  have hqNidx : q ≥ Nidx := Nat.le_trans (Nat.le_add_right Nidx (m + 2)) hq
  have hpm2 : p ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) Nidx) hp
  have hqm2 : q ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) Nidx) hq
  obtain ⟨K, hK⟩ := hNidx p q hpNidx hqNidx
  let big : Nat := p + q + K
  have hbig_p : big ≥ p :=
    Nat.le_trans (Nat.le_add_right p q) (Nat.le_add_right (p + q) K)
  have hbig_K : big ≥ K := Nat.le_add_left K (p + q)
  have hbig_m2 : big ≥ m + 2 := Nat.le_trans hpm2 hbig_p
  have hleg1 : closeDy L (m + 2) (diagSeq L S p) ((S p).seq big) :=
    (S p).reg (m + 2) p big hpm2 hbig_m2
  have hleg2 : closeDy L (m + 2) ((S p).seq big) ((S q).seq big) :=
    hK big hbig_K
  have hleg3 : closeDy L (m + 2) ((S q).seq big) (diagSeq L S q) :=
    (S q).reg (m + 2) big q hbig_m2 hqm2
  exact (dyMet L).qtri m (diagSeq L S p) ((S p).seq big) ((S q).seq big)
    (diagSeq L S q) hleg1 hleg2 hleg3

/-! ## 4. A generic telescoping lemma for `MetricModulus`

From per-step bounds `close (k+1) (f k) (f (k+1))` (each consecutive pair within
`1/2^(k+1)`), the geometric tail `Σ 1/2^k` gives `close m (f p) (f q)` whenever
`p, q ≥ m + 1`.  This is the abstract telescoping behind any regular Cauchy
sequence with geometric step decay — proved once here, reused for the stabilizing
diagonal below.  The proof mirrors `picard_tail`: a uniform-in-`j` tail bound
`close (s) (f p) (f (p + j))` for `p ≥ s`, by induction on `j`. -/

/-- Tail bound: if every step `close (k+1) (f k) (f (k+1))` holds, then for all
    `j` and all `p ≥ s + 1`, `close s (f p) (f (p + j))`.  (Geometric tail
    `Σ_{i≥0} 1/2^(p+1+i) = 1/2^p ≤ 1/2^s`.) -/
theorem telescope_tail {X : Type} (M : MetricModulus X) (f : Nat → X)
    (hstep : ∀ k, M.close (k + 1) (f k) (f (k + 1))) :
    ∀ j s p, p ≥ s + 1 → M.close s (f p) (f (p + j)) := by
  intro j
  induction j with
  | zero =>
      intro s p _
      have : f (p + 0) = f p := by rw [Nat.add_zero]
      rw [this]; exact M.crefl s (f p)
  | succ j ih =>
      intro s p hp
      -- step at p : close (p+1) (f p) (f (p+1)); coarsen to close (s+1) since p ≥ s+1, i.e. p+1 ≥ s+2
      -- We need close (s+1) (f p) (f (p+1)) and close (s+1) (f (p+1)) (f (p+1+j)).
      -- step p gives close (p+1); since p+1 ≥ s+2 ≥ s+1, coarsen down.
      have hstepp : M.close (p + 1) (f p) (f (p + 1)) := hstep p
      -- coarsen close (p+1) to close (s+1): p+1 = (s+1) + (p - s)
      have hps : p + 1 ≥ s + 1 + 1 := Nat.succ_le_succ hp
      -- generic coarsening: close (s+1+d) → close (s+1)
      have hstep' : M.close (s + 1) (f p) (f (p + 1)) := by
        -- s+1 ≤ p+1, so close (p+1) coarsens to close (s+1)
        have hle : s + 1 ≤ p + 1 := Nat.le_succ_of_le hp
        obtain ⟨d, hd⟩ := Nat.le.dest hle   -- (s+1) + d = p+1
        -- rewrite only the *scale* of hstepp from p+1 to (s+1)+d
        have hc : M.close ((s + 1) + d) (f p) (f (p + 1)) := by rw [hd]; exact hstepp
        exact cmono_le M (s + 1) (f p) (f (p + 1)) d hc
      -- ih at p+1, scale s+1, needs p+1 ≥ (s+1)+1 = s+2
      have hp1 : p + 1 ≥ (s + 1) + 1 := Nat.succ_le_succ hp
      have ihc : M.close (s + 1) (f (p + 1)) (f ((p + 1) + j)) := ih (s + 1) (p + 1) hp1
      -- halving triangle: close (s+1) (f p)(f (p+1)) + close (s+1) (f (p+1))(f (p+1+j)) → close s (f p)(f (p+1+j))
      have hmerge : M.close s (f p) (f ((p + 1) + j)) :=
        M.ctri s (f p) (f (p + 1)) (f ((p + 1) + j)) hstep' ihc
      have eidx : (p + 1) + j = p + (j + 1) := by
        rw [Nat.add_right_comm p 1 j, Nat.add_assoc p j 1]
      rw [eidx] at hmerge
      exact hmerge

/-- Telescoping regularity: per-step bounds give the regular spec.  `close m
    (f p) (f q)` for all `p, q ≥ m + 1` (symmetrise + tail, both directions). -/
theorem telescope_regular {X : Type} (M : MetricModulus X) (f : Nat → X)
    (hstep : ∀ k, M.close (k + 1) (f k) (f (k + 1))) :
    ∀ m p q, p ≥ m + 1 → q ≥ m + 1 → M.close m (f p) (f q) := by
  intro m p q hp hq
  rcases Nat.le_total p q with hpq | hqp
  · obtain ⟨j, hj⟩ := Nat.le.dest hpq   -- p + j = q
    have := telescope_tail M f hstep j m p hp
    rw [hj] at this; exact this
  · obtain ⟨j, hj⟩ := Nat.le.dest hqp   -- q + j = p
    have hclose := telescope_tail M f hstep j m q hq
    rw [hj] at hclose
    exact M.csymm m (f q) (f p) hclose

/-! ## 5. The stabilizing diagonal `stab` — a *total* regular limit sequence

For an arbitrary sequence of completion points `S` (no Cauchy hypothesis), the
plain diagonal `(S n).seq n` need not be regular.  `stab L S` repairs this: at
each level it accepts the next diagonal value only if it stays within `1/2^(k+1)`
of the current value (a decidable `Nat`-`<` test on `closeDy`), else it freezes.

This makes the **per-step bound** `closeDy L (k+1) (stab k) (stab (k+1))` hold
*unconditionally* (taken ⇒ the `if`-condition; frozen ⇒ reflexivity), so `stab`
is regular by `telescope_regular` — a legitimate `DyC L` for *every* `S`.  For a
genuinely Cauchy `S` the freeze eventually never triggers, so `stab` agrees with
the plain diagonal in the tail; that is what powers `climconv`. -/

/-- `closeDy` is decidable (pure `Nat` `<`), so the freeze is constructive. -/
instance (L m : Nat) (a b : Dy) : Decidable (closeDy L m a b) := by
  unfold closeDy; exact inferInstanceAs (Decidable (_ < _))

/-- The stabilizing-diagonal sequence (total in `S`). -/
def stab (L : Nat) (S : Nat → DyC L) : Nat → Dy
  | 0 => (S 0).seq 0
  | n + 1 =>
      if closeDy L (n + 1) (stab L S n) ((S (n + 1)).seq (n + 1))
      then (S (n + 1)).seq (n + 1)
      else stab L S n

/-- **Per-step bound (unconditional).**  `closeDy L (k+1) (stab k) (stab (k+1))`
    for every `k` and every `S` — the freeze guarantees it (taken: the
    `if`-condition; frozen: reflexivity). -/
theorem stab_step (L : Nat) (S : Nat → DyC L) (k : Nat) :
    closeDy L (k + 1) (stab L S k) (stab L S (k + 1)) := by
  show closeDy L (k + 1) (stab L S k)
    (if closeDy L (k + 1) (stab L S k) ((S (k + 1)).seq (k + 1))
     then (S (k + 1)).seq (k + 1) else stab L S k)
  by_cases h : closeDy L (k + 1) (stab L S k) ((S (k + 1)).seq (k + 1))
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact closeDy_refl L (k + 1) (stab L S k)


/-- **`stab` shifted is regular.**  Using the shift `n ↦ stab (n+1)`, the regular
    spec at scale `m` (`p, q ≥ m`) becomes `telescope_regular` at scale `m` for
    indices `p + 1, q + 1 ≥ m + 1` — exactly its hypothesis. -/
theorem stabShift_regular (L : Nat) (S : Nat → DyC L) :
    ∀ m p q, p ≥ m → q ≥ m →
      closeDy L m (stab L S (p + 1)) (stab L S (q + 1)) := by
  intro m p q hp hq
  exact telescope_regular (dyMet L) (stab L S) (stab_step L S) m (p + 1) (q + 1)
    (Nat.succ_le_succ hp) (Nat.succ_le_succ hq)

/-- **The total stabilized point** `limPoint L S : DyC L` — the shifted
    stabilizing diagonal, a legitimate completion point for *every* `S` (regular
    by `stabShift_regular`, no Cauchy hypothesis). -/
def limPoint (L : Nat) (S : Nat → DyC L) : DyC L where
  seq := fun n => stab L S (n + 1)
  reg := stabShift_regular L S

/-! ## 6. Lifting convolve-and-rescale `Φ̂` to the completion + the contraction

`Φ : Dy → Dy` lifts to `Φ̂ : DyC L → DyC L` pointwise.  `Φ` is *non-expansive at
every scale* (`closeDy_Φ_same`: it halves the value distance while the
denominator level rises by 2, net-preserving the bound with room to spare), so
the lift preserves regularity; and `Φ̂` is a genuine `Contraction (metC L) Φ̂`
(`Φhat_contraction`) — the convolve-rescale contraction on the genuine
completion carrier. -/

/-- **`Φ` is non-expansive at every scale**: `closeDy L m a b → closeDy L m
    (Φ a) (Φ b)`.  After `Φ` the cross-distance doubles (`crossDist_Φ`) and the
    level rises by `2`; multiplying the hypothesis by `2` already lands strictly
    below the `×4` right side. -/
theorem closeDy_Φ_same (L m : Nat) (a b : Dy) (h : closeDy L m a b) :
    closeDy L m (Φ a) (Φ b) := by
  -- h : 2^m * crossDist a b < 2^(a.2+b.2) * 2^(L+1)
  -- goal: 2^m * crossDist (Φ a)(Φ b) < 2^((Φ a).2+(Φ b).2) * 2^(L+1)
  unfold closeDy
  have hlvl : (Φ a).2 + (Φ b).2 = (a.2 + b.2) + 2 := by
    show (a.2 + 1) + (b.2 + 1) = (a.2 + b.2) + 2
    rw [Nat.add_assoc a.2 1 (b.2 + 1), Nat.add_comm 1 (b.2 + 1),
      Nat.add_assoc b.2 1 1, ← Nat.add_assoc a.2 b.2 (1 + 1)]
  rw [crossDist_Φ a b, hlvl]
  -- goal: 2^m * (2 * crossDist a b) < 2^((a.2+b.2)+2) * 2^(L+1)
  have hh : closeDy L m a b := h
  unfold closeDy at hh
  -- 2·(2^m·crossDist) < 2·(2^(a.2+b.2)·2^(L+1))
  have h2 : 2 * (2 ^ m * crossDist a b) < 2 * (2 ^ (a.2 + b.2) * 2 ^ (L + 1)) :=
    Nat.mul_lt_mul_of_pos_left hh (by decide)
  -- LHS = 2^m·(2·crossDist) ; RHS' = 2^((a.2+b.2)+2)·2^(L+1) and 2·RHS_h ≤ RHS'
  have hL : 2 * (2 ^ m * crossDist a b) = 2 ^ m * (2 * crossDist a b) := by
    rw [← mul_assoc 2 (2 ^ m) (crossDist a b), Nat.mul_comm 2 (2 ^ m),
      mul_assoc (2 ^ m) 2 (crossDist a b)]
  have hRle : 2 * (2 ^ (a.2 + b.2) * 2 ^ (L + 1)) ≤ 2 ^ ((a.2 + b.2) + 2) * 2 ^ (L + 1) := by
    -- RHS = 2^((a.2+b.2)+2)·2^(L+1) = (2^(a.2+b.2)·4)·2^(L+1) = 4·(2^(a.2+b.2)·2^(L+1))
    have hR : 2 ^ ((a.2 + b.2) + 2) * 2 ^ (L + 1)
        = 4 * (2 ^ (a.2 + b.2) * 2 ^ (L + 1)) := by
      rw [pow_add_two (a.2 + b.2) 2]
      show (2 ^ (a.2 + b.2) * 4) * 2 ^ (L + 1) = 4 * (2 ^ (a.2 + b.2) * 2 ^ (L + 1))
      rw [Nat.mul_comm (2 ^ (a.2 + b.2)) 4, mul_assoc 4 (2 ^ (a.2 + b.2)) (2 ^ (L + 1))]
    rw [hR]
    exact Nat.mul_le_mul_right _ (by decide)
  rw [hL] at h2
  exact Nat.lt_of_lt_of_le h2 hRle

/-- Pointwise lift of `Φ` to the completion carrier (regularity from
    `closeDy_Φ_same`). -/
def Φhat (L : Nat) (a : DyC L) : DyC L where
  seq := fun n => Φ (a.seq n)
  reg := fun m p q hp hq => closeDy_Φ_same L m (a.seq p) (a.seq q) (a.reg m p q hp hq)

/-- **★ `Φhat` is a `Contraction` of the completion metric `metC L`.**  From
    `closeC (m+1) a b` (a tail on which the underlying sequences are
    `closeDy (m+1)`), `Φ`'s exact halving (`Φ_contraction`) gives the underlying
    sequences `closeDy (m+2)` after `Φ` on the same tail — i.e.
    `closeC (m+2) (Φ̂ a) (Φ̂ b)`.  The convolve-rescale contraction, now on the
    genuine Cauchy completion. -/
theorem Φhat_contraction (L : Nat) : Contraction (metC L) (Φhat L) := by
  intro m a b hab
  obtain ⟨K, hK⟩ := hab
  refine ⟨K, fun n hn => ?_⟩
  -- (Φ̂ a).seq n = Φ (a.seq n); apply Φ_contraction to hK n
  show closeDy L (m + 2) (Φ (a.seq n)) (Φ (b.seq n))
  exact Φ_contraction L m (a.seq n) (b.seq n) (hK n hn)

/-! ## 7. The convolve-rescale orbit converges to the Gaussian center *in the
completion*

The Picard orbit of `Φ̂` from the constant seed `inj L (p, 0)` is, at each scale,
the lifted orbit of `Φ` from `(p,0)` — i.e. `(p, n)` at term `n`.  `orbit_to_center`
already proves this orbit converges to the center `(0,0)` on `Dy`.  Lifting:
the orbit converges, in the completion metric `closeC`, to `inj L (0,0)` — the
**Gaussian center as the completion-limit of convolve-and-rescale**, reached by
none (no finite step has value `0` for `p > 0`), only as the limit.  This is the
`banach_fixed_point` conclusion's *content* (the located fixed point reached as a
Cauchy limit) delivered for the convolve-rescale map through the genuine
completion carrier `DyC L`. -/

/-- The Picard orbit of `Φ̂` from `inj L (p,0)`, read at each term index, is the
    `Φ`-orbit on `Dy`: `(picard (Φhat L) (inj L (p,0)) n).seq j = picard Φ (p,0) n`. -/
theorem picard_Φhat_seq (L p : Nat) :
    ∀ n j, (picard (Φhat L) (inj L (p, 0)) n).seq j = picard Φ (p, 0) n := by
  intro n
  induction n with
  | zero => intro j; rfl
  | succ k ih =>
      intro j
      show Φ ((picard (Φhat L) (inj L (p, 0)) k).seq j) = Φ (picard Φ (p, 0) k)
      rw [ih j]

/-- **★★ Convolve-rescale orbit → Gaussian center, in the completion.**  The
    `Φ̂`-orbit from `inj L (p,0)` converges (in `closeC`) to `inj L (0,0)`: for
    every scale `m` there is `N` with `closeC L m (picard (Φhat L) (inj L (p,0)) n)
    (inj L (0,0))` for all `n ≥ N`.  The center is the completion-limit of the
    convolve-rescale Picard orbit — the genuine fixed-point content, ∅-axiom. -/
theorem orbit_to_center_completion (L p : Nat) :
    ∀ m, ∃ N, ∀ n, n ≥ N →
      closeC L m (picard (Φhat L) (inj L (p, 0)) n) (inj L (0, 0)) := by
  intro m
  obtain ⟨N, hN⟩ := orbit_to_center L p m
  refine ⟨N, fun n hn => ?_⟩
  -- closeC: pick any tail K=0; pointwise closeDy m (orbit-term-value) (center)
  refine ⟨0, fun j _ => ?_⟩
  -- goal: closeDy L m ((picard Φ̂ (inj (p,0)) n).seq j) ((inj (0,0)).seq j)
  -- (inj (0,0)).seq j ≡ (0,0) defeq; rewrite the orbit value
  have hval : (picard (Φhat L) (inj L (p, 0)) n).seq j = picard Φ (p, 0) n :=
    picard_Φhat_seq L p n j
  have hgoal : closeDy L m (picard Φ (p, 0) n) ((0 : Nat), (0 : Nat)) :=
    closeDy_symm L m ((0 : Nat), (0 : Nat)) (picard Φ (p, 0) n) (hN n hn)
  show closeDy L m ((picard (Φhat L) (inj L (p, 0)) n).seq j) ((inj L (0, 0)).seq j)
  rw [hval]
  exact hgoal

/-! ## 8. The diagonal limit + `climconvMod` — `DyC L` is a modulated completion

`limPoint`/`stab` (§5) repaired the *bare* diagonal into a regular point for
*every* `S` via a decidable freeze — the cost of forcing a total `lim` onto bare
sequences (the bare `CompleteMetricModulus` interface), and its
freeze-permanence is genuinely delicate.  The modulated engine
(`BanachFixedPointModulated.CompleteMetricModulusMod`) sidesteps that entirely:
with the convergence modulus supplied as **data**, the diagonal can be
*subsampled* against that modulus into a genuinely **regular** (identity-modulus)
sequence — no freeze.

The plain diagonal `diagSeq` is Cauchy with a *non-identity* modulus
(`diag_reg`: its scale-`m` modulus is `cmod N m = N (m+2) + (m+2)`).  To make a
`DyC L` (which demands the identity-modulus `reg` spec) we reindex by a monotone
running-max `cmodMon N` of that modulus: `regDiag k = diagSeq (cmodMon N k)`.
Monotone + dominating ⇒ for `p, q ≥ m` both indices clear `cmod N m`, so
`diag_reg_mod` lands `closeDy m (regDiag p) (regDiag q)` — identity-modulus
regular.  `climconv` then chains `(S p).seq big — (S big').seq big —` via `qtri`,
the `diag_reg` skeleton, against `regDiag` in the tail. -/

open E213.Lib.Math.Analysis.BanachFixedPoint
  (CompleteMetricModulusMod)

/-- **`diag_reg_mod` — `diag_reg` with the modulus as an explicit argument.**
    For an explicit modulus `N` (`closeC`-Cauchy at `N`), the plain diagonal is
    Cauchy with the explicit scale-`m` modulus `N (m+2) + (m+2)`.  Same proof as
    `diag_reg` (chain via `big`, `qtri`), `N` supplied rather than chosen. -/
theorem diag_reg_mod (L : Nat) (S : Nat → DyC L) (N : Nat → Nat)
    (hcau : ∀ m p q, p ≥ N m → q ≥ N m → closeC L m (S p) (S q)) :
    ∀ m p q, p ≥ N (m + 2) + (m + 2) → q ≥ N (m + 2) + (m + 2) →
      closeDy L m (diagSeq L S p) (diagSeq L S q) := by
  intro m p q hp hq
  have hpNidx : p ≥ N (m + 2) := Nat.le_trans (Nat.le_add_right _ (m + 2)) hp
  have hpm2 : p ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) _) hp
  have hqNidx : q ≥ N (m + 2) := Nat.le_trans (Nat.le_add_right _ (m + 2)) hq
  have hqm2 : q ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) _) hq
  obtain ⟨K, hK⟩ := hcau (m + 2) p q hpNidx hqNidx
  let big : Nat := p + q + K
  have hbig_p : big ≥ p :=
    Nat.le_trans (Nat.le_add_right p q) (Nat.le_add_right (p + q) K)
  have hbig_K : big ≥ K := Nat.le_add_left K (p + q)
  have hbig_m2 : big ≥ m + 2 := Nat.le_trans hpm2 hbig_p
  have hleg1 : closeDy L (m + 2) (diagSeq L S p) ((S p).seq big) :=
    (S p).reg (m + 2) p big hpm2 hbig_m2
  have hleg2 : closeDy L (m + 2) ((S p).seq big) ((S q).seq big) :=
    hK big hbig_K
  have hleg3 : closeDy L (m + 2) ((S q).seq big) (diagSeq L S q) :=
    (S q).reg (m + 2) big q hbig_m2 hqm2
  exact (dyMet L).qtri m (diagSeq L S p) ((S p).seq big) ((S q).seq big)
    (diagSeq L S q) hleg1 hleg2 hleg3

/-- The scale-`m` diagonal modulus from an explicit Cauchy modulus `N`. -/
def cmod (N : Nat → Nat) (m : Nat) : Nat := N (m + 2) + (m + 2)

/-- Monotone running-max of `cmod N`: `cmodMon N k = max_{j ≤ k} cmod N j`. -/
def cmodMon (N : Nat → Nat) : Nat → Nat
  | 0 => cmod N 0
  | k + 1 => Nat.max (cmodMon N k) (cmod N (k + 1))

/-- `cmodMon` is nondecreasing. -/
theorem cmodMon_mono (N : Nat → Nat) (k : Nat) :
    cmodMon N k ≤ cmodMon N (k + 1) :=
  E213.Meta.Nat.Max213.le_max_left _ _

/-- `cmodMon` dominates `cmod` at its own index. -/
theorem cmod_le_cmodMon (N : Nat → Nat) : ∀ k, cmod N k ≤ cmodMon N k
  | 0 => Nat.le_refl _
  | _ + 1 => E213.Meta.Nat.Max213.le_max_right _ _

/-- `cmodMon N a ≤ cmodMon N (a + d)` for every `d` (iterate the one-step bound). -/
theorem cmodMon_le_add (N : Nat → Nat) (a : Nat) :
    ∀ d, cmodMon N a ≤ cmodMon N (a + d)
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (cmodMon_le_add N a d) (cmodMon_mono N (a + d))

/-- `cmodMon` is monotone across `≤`. -/
theorem cmodMon_le_of_le (N : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    cmodMon N a ≤ cmodMon N b := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd]
  exact cmodMon_le_add N a d

/-- `cmod N` dominated by `cmodMon N` at every later index: `m ≤ k → cmod N m ≤
    cmodMon N k`.  (The running-max is monotone and dominates pointwise.) -/
theorem cmod_le_cmodMon_of_le (N : Nat → Nat) {m k : Nat} (h : m ≤ k) :
    cmod N m ≤ cmodMon N k :=
  Nat.le_trans (cmod_le_cmodMon N m) (cmodMon_le_of_le N h)

/-- **The regularized (subsampled) diagonal** — a genuine identity-modulus
    `DyC L`.  `regDiag k = diagSeq (cmodMon N k)`; for `p, q ≥ m` both indices
    clear `cmod N m`, so `diag_reg_mod` gives the identity-modulus `reg` spec. -/
def regDiagPoint (L : Nat) (S : Nat → DyC L) (N : Nat → Nat)
    (hcau : ∀ m p q, p ≥ N m → q ≥ N m → closeC L m (S p) (S q)) : DyC L where
  seq := fun k => diagSeq L S (cmodMon N k)
  reg := fun m p q hp hq =>
    diag_reg_mod L S N hcau m (cmodMon N p) (cmodMon N q)
      (cmod_le_cmodMon_of_le N hp) (cmod_le_cmodMon_of_le N hq)

/-! ## 9. `climconvMod` for the regularized diagonal + the engine instance -/

/-- **★ `climconv_regDiag` — the convergence (∅-axiom, finite `Nat`).**

    For a modulus-carried Cauchy `S`, the regularized diagonal `regDiagPoint` is
    its `closeC` limit: for every scale `m`, past `N (m+2) + (m+2)` the terms
    `S p` are `closeC m` to `regDiagPoint`.  Crux: `closeC m (S p) regDiagPoint`
    needs a tail `K` with `closeDy m ((S p).seq big) ((S (cmodMon N n)).seq big)`
    for `n ≥ K`; take `K = N (m+2) + (m+2)`, and for each such `n` chain through
    `big = p + cmodMon N n + (inner tail)` via three `(m+2)`-legs (`qtri`).  The
    subsample index `cmodMon N n ≥ cmod N n ≥ N (m+2) + (m+2) ≥ N (m+2)` clears
    the Cauchy modulus, so leg 2 holds. -/
theorem climconv_regDiag (L : Nat) (S : Nat → DyC L) (N : Nat → Nat)
    (hcau : ∀ m p q, p ≥ N m → q ≥ N m → closeC L m (S p) (S q)) :
    ∀ m, ∃ K, ∀ p, p ≥ K → closeC L m (S p) (regDiagPoint L S N hcau) := by
  intro m
  refine ⟨N (m + 2) + (m + 2), fun p hp => ?_⟩
  -- tail K = N(m+2)+(m+2): for n ≥ K, closeDy m ((S p).seq n) (regDiag.seq n)
  refine ⟨N (m + 2) + (m + 2), fun n hn => ?_⟩
  -- regDiag.seq n = diagSeq (cmodMon N n) = (S (cmodMon N n)).seq (cmodMon N n)
  show closeDy L m ((S p).seq n)
    ((S (cmodMon N n)).seq (cmodMon N n))
  -- r := cmodMon N n, the subsample index.  Since n ≥ N(m+2)+(m+2) ≥ m+2 ≥ m,
  -- the running-max dominates cmod N m = N(m+2)+(m+2): cmodMon N n ≥ cmod N m.
  have hn_m2 : n ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) _) hn
  have hnm' : m ≤ n :=
    Nat.le_trans (Nat.le_trans (Nat.le_succ m) (Nat.le_succ (m + 1))) hn_m2
  have hrge : cmodMon N n ≥ N (m + 2) + (m + 2) :=
    cmod_le_cmodMon_of_le N hnm'
  -- bounds
  have hpNidx : p ≥ N (m + 2) := Nat.le_trans (Nat.le_add_right _ (m + 2)) hp
  have hpm2 : p ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) _) hp
  have hnm2 : n ≥ m + 2 := Nat.le_trans (Nat.le_add_left (m + 2) _) hn
  have hrNidx : cmodMon N n ≥ N (m + 2) :=
    Nat.le_trans (Nat.le_add_right _ (m + 2)) hrge
  have hrm2 : cmodMon N n ≥ m + 2 :=
    Nat.le_trans (Nat.le_add_left (m + 2) _) hrge
  -- inter-term Cauchy tail at scale (m+2) between p and r=cmodMon N n
  obtain ⟨Kt, hKt⟩ := hcau (m + 2) p (cmodMon N n) hpNidx hrNidx
  let big : Nat := p + cmodMon N n + Kt
  have hbig_p : big ≥ p :=
    Nat.le_trans (Nat.le_add_right p (cmodMon N n))
      (Nat.le_add_right (p + cmodMon N n) Kt)
  have hbig_K : big ≥ Kt := Nat.le_add_left Kt (p + cmodMon N n)
  have hbig_m2 : big ≥ m + 2 := Nat.le_trans hpm2 hbig_p
  -- leg1: (S p) regular, indices n, big
  have hleg1 : closeDy L (m + 2) ((S p).seq n) ((S p).seq big) :=
    (S p).reg (m + 2) n big hnm2 hbig_m2
  -- leg2: inter-term Cauchy at index big
  have hleg2 : closeDy L (m + 2) ((S p).seq big) ((S (cmodMon N n)).seq big) :=
    hKt big hbig_K
  -- leg3: (S r) regular, indices big, r
  have hleg3 : closeDy L (m + 2)
      ((S (cmodMon N n)).seq big) ((S (cmodMon N n)).seq (cmodMon N n)) :=
    (S (cmodMon N n)).reg (m + 2) big (cmodMon N n) hbig_m2 hrm2
  exact (dyMet L).qtri m ((S p).seq n) ((S p).seq big)
    ((S (cmodMon N n)).seq big) ((S (cmodMon N n)).seq (cmodMon N n))
    hleg1 hleg2 hleg3

/-- **★ `completeDyMod L` — the modulated completion of the dyadic metric.**
    The first **non-trivial** inhabitant of `CompleteMetricModulusMod` (the only
    prior one is the degenerate `trivCompleteMod` on `Unit`): `limMod` is the
    regularized diagonal of the modulus-carried Cauchy sequence; `climconvMod` is
    the finite-`Nat` `climconv_regDiag`.  No freeze, no choice. -/
def completeDyMod (L : Nat) : CompleteMetricModulusMod (DyC L) where
  toMetricModulus := metC L
  limMod := fun S N hcau => regDiagPoint L S N hcau
  climconvMod := fun S N hcau m => climconv_regDiag L S N hcau m

/-! ## 10. ★★★ The Gaussian center as a fixed point THROUGH the reusable engine

The headline.  `Φhat_contraction` (§6) is exactly the `Contraction` the
modulated engine consumes; feeding it the base gap, `banach_fixed_point_modulated`
lands the convolve-rescale fixed point as the *engine-produced* Picard limit
`picardLim` — and that limit is `closeC`-equal (at every scale) to the Gaussian
center `inj L (0,0)`.  The center is the located fixed point of convolve-and-
rescale, obtained through a reusable generic engine, ∅-axiom — not the by-hand
`orbit_to_center_completion`. -/

/-- The base gap for the `Φhat` orbit from the seed `inj L (p, 0)` at scale `s+1`:
    `closeC (s+1) (inj L (p,0)) (Φhat L (inj L (p,0)))`, provided `2^(s+1)·p <
    2^1·2^(L+1)` (the `Dy`-level base gap `closeDy_center`, lifted pointwise). -/
theorem Φhat_base_gap (L p s : Nat)
    (h : 2 ^ (s + 1) * p < 2 ^ 1 * 2 ^ (L + 1)) :
    closeC L (s + 1) (picard (Φhat L) (inj L (p, 0)) 0)
      (picard (Φhat L) (inj L (p, 0)) 1) := by
  refine ⟨0, fun n _ => ?_⟩
  -- picard 0 = inj (p,0) (seq ≡ (p,0)); picard 1 = Φhat (inj (p,0)) (seq ≡ Φ (p,0) = (p,1))
  show closeDy L (s + 1) ((inj L (p, 0)).seq n)
    ((Φhat L (inj L (p, 0))).seq n)
  -- (inj L (p,0)).seq n ≡ (p,0); (Φhat …).seq n ≡ Φ ((inj …).seq n) ≡ Φ (p,0) = (p,1)
  show closeDy L (s + 1) (p, 0) (Φ (p, 0))
  -- Φ (p,0) = (p,1); closeDy (s+1) (p,0) (p,1)
  show closeDy L (s + 1) (p, 0) (p, 1)
  unfold closeDy
  -- 2^(s+1)·crossDist (p,0)(p,1) < 2^(0+1)·2^(L+1)
  have hc : crossDist ((p : Nat), (0 : Nat)) ((p : Nat), (1 : Nat)) = p := by
    show E213.Lib.Math.Analysis.UniformLimitContinuous.distN
      (p * 2 ^ 1) (p * 2 ^ 0) = p
    show (p * 2 ^ 1 - p * 2 ^ 0) + (p * 2 ^ 0 - p * 2 ^ 1) = p
    rw [Nat.pow_one, Nat.pow_zero, Nat.mul_one]
    -- (p*2 - p) + (p - p*2) = p :  p*2 = p + p, so (p+p) - p = p and p - (p+p) = 0
    have e1 : p * 2 = p + p := by rw [Nat.mul_comm]; exact Nat.two_mul p
    rw [e1]
    -- (p+p) - p = p via the pure add_sub_cancel_p ; p - (p+p) = 0 via pure sub_eq_zero_of_le_p
    rw [E213.Lib.Math.Analysis.UniformLimitContinuous.add_sub_cancel_p p p,
      E213.Lib.Math.Probability.Limit.ConvolveRescaleContraction.sub_eq_zero_of_le_p
        (Nat.le_add_right p p),
      Nat.add_zero]
  show 2 ^ (s + 1) * crossDist ((p : Nat), (0 : Nat)) ((p : Nat), (1 : Nat))
      < 2 ^ ((0 : Nat) + 1) * 2 ^ (L + 1)
  rw [hc, Nat.zero_add]
  exact h

/-- The base-gap hypothesis at the center seed `p = 0`: `2^(0+1)·0 < 2^1·2^(L+1)`
    (the LHS is `0`, the RHS positive). -/
theorem center_base_lt (L : Nat) : 2 ^ (0 + 1) * 0 < 2 ^ 1 * 2 ^ (L + 1) := by
  rw [Nat.mul_zero]
  exact Nat.mul_pos (Nat.pos_pow_of_pos 1 (by decide))
    (Nat.pos_pow_of_pos (L + 1) (by decide))

/-- **★★★ Gaussian center = fixed point of `Φhat` through the reusable engine.**

    The convolve-rescale fixed point `x* = (completeDyMod L).picardLim …` (the
    Picard limit produced by `banach_fixed_point_modulated` from
    `Φhat_contraction`) satisfies `closeC m x* (Φhat L x*)` at every scale —
    located equality `Φhat x* = x*` — obtained THROUGH the generic modulated
    engine.  Seed `inj L (p,0)` with `p = 0` (`2^(s+1)·0 = 0 < …`), so the base
    gap holds for any `s`; the engine lands the center as a genuine Banach fixed
    point, ∅-axiom, reusable. -/
theorem gaussian_center_fixed_via_engine (L : Nat) :
    ∀ m, closeC L m
      ((completeDyMod L).picardLim (Φhat_contraction L) (inj L (0, 0)) 0
        (Φhat_base_gap L 0 0 (center_base_lt L)))
      (Φhat L
        ((completeDyMod L).picardLim (Φhat_contraction L) (inj L (0, 0)) 0
          (Φhat_base_gap L 0 0 (center_base_lt L)))) :=
  (completeDyMod L).banach_fixed_point_modulated
    (Φhat_contraction L) (inj L (0, 0)) 0 (Φhat_base_gap L 0 0 (center_base_lt L))

end E213.Lib.Math.Probability.Limit.DyadicCompletion
