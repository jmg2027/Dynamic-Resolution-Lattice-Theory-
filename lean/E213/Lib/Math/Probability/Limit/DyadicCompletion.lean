import E213.Lib.Math.Probability.Limit.ConvolveRescaleContraction

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
is the named follow-on, tracked in `research-notes/frontiers/wall_synthesis.md`;
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

end E213.Lib.Math.Probability.Limit.DyadicCompletion
