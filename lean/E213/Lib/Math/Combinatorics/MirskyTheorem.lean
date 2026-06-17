import E213.Meta.Nat.Max213
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.Combinatorics.Pigeonhole

/-!
# Mirsky's theorem via the computed height function (∅-axiom)

A finite poset on `Fin n` (`le : Fin n → Fin n → Bool`, reflexive /
transitive / antisymmetric).  `height i = 1 + max { height j : j ≺ i }`,
the longest strict chain ending at `i`, computed by a fuel-bounded fold
mirroring `ErdosSzekeres.incVal` / `maxBelow`.

Mirsky: elements of equal height form an antichain; the number of
distinct heights = the longest chain length, so the poset is partitioned
into `(max height)` antichains — the level sets `height⁻¹(k)`, read off
the computed heights, not asserted.
-/

open E213.Meta.Nat.Max213

namespace E213.Lib.Math.Combinatorics.MirskyTheorem

/-! ## Poset structure -/

/-- `le` is reflexive, transitive, antisymmetric: a finite poset on `Fin n`. -/
structure IsPoset (n : Nat) (le : Fin n → Fin n → Bool) : Prop where
  refl  : ∀ i, le i i = true
  trans : ∀ i j k, le i j = true → le j k = true → le i k = true
  antisymm : ∀ i j, le i j = true → le j i = true → i = j

/-- Strict order `j ≺ i`: `le j i ∧ j ≠ i`. -/
def lt {n : Nat} (le : Fin n → Fin n → Bool) (j i : Fin n) : Prop :=
  le j i = true ∧ j ≠ i

/-! ## Bounded max over the first `m` Fin-indices

`fmax n f m = max { f ⟨k,_⟩ : k < m }`, empty = 0.  Pure fold mirroring
`ErdosSzekeres.bmax`. -/

/-- `fmax f m = max_{k<m} f ⟨k,·⟩`, empty = 0. -/
def fmax {n : Nat} (f : Fin n → Nat) : Nat → Nat
  | 0 => 0
  | m+1 => Nat.max (fmax f m) (if h : m < n then f ⟨m, h⟩ else 0)

/-- Every in-range entry `f ⟨k,_⟩` with `k < m` is `≤ fmax f m`. -/
theorem le_fmax {n : Nat} (f : Fin n → Nat) :
    ∀ (m k : Nat) (hk : k < n), k < m → f ⟨k, hk⟩ ≤ fmax f m
  | 0, _, _, hkm => absurd hkm (Nat.not_lt_zero _)
  | m+1, k, hk, hkm => by
    show f ⟨k, hk⟩ ≤ Nat.max (fmax f m) (if h : m < n then f ⟨m, h⟩ else 0)
    rcases Nat.lt_or_ge k m with hlt | hge
    · exact Nat.le_trans (le_fmax f m k hk hlt) (le_max_left _ _)
    · have hkm' : k = m := Nat.le_antisymm (Nat.le_of_lt_succ hkm) hge
      have : f ⟨k, hk⟩ = (if h : m < n then f ⟨m, h⟩ else 0) := by
        subst hkm'; rw [dif_pos hk]
      rw [this]; exact le_max_right _ _

/-- `fmax` is attained: it is `0`, or equals some in-range `f ⟨k,_⟩` with `k < m`. -/
theorem fmax_attained {n : Nat} (f : Fin n → Nat) :
    ∀ (m : Nat),
      fmax f m = 0 ∨ ∃ (k : Nat) (hk : k < n), k < m ∧ f ⟨k, hk⟩ = fmax f m
  | 0 => Or.inl rfl
  | m+1 => by
    rcases Nat.lt_or_ge m n with hmn | hmn
    · -- the (m+1)-th slot is a real entry f ⟨m, hmn⟩
      have hunf : fmax f (m+1) = Nat.max (fmax f m) (f ⟨m, hmn⟩) := by
        show Nat.max (fmax f m) (if h : m < n then f ⟨m, h⟩ else 0)
              = Nat.max (fmax f m) (f ⟨m, hmn⟩)
        rw [dif_pos hmn]
      rw [hunf]
      rcases Nat.lt_or_ge (fmax f m) (f ⟨m, hmn⟩) with hlt | hge
      · -- max = f ⟨m,_⟩, attained at m
        have hmax : Nat.max (fmax f m) (f ⟨m, hmn⟩) = f ⟨m, hmn⟩ := by
          rw [E213.Meta.Nat.AddMod213.max_comm]
          exact max_eq_left (Nat.le_of_lt hlt)
        exact Or.inr ⟨m, hmn, Nat.lt_succ_self m, hmax.symm⟩
      · -- max = fmax f m
        have hmax : Nat.max (fmax f m) (f ⟨m, hmn⟩) = fmax f m := max_eq_left hge
        rcases fmax_attained f m with h0 | ⟨k, hk, hkm, hfk⟩
        · -- fmax f m = 0 ⟹ f ⟨m,_⟩ = 0 too ⟹ max = f ⟨m,_⟩, attained at m
          have hfm0 : f ⟨m, hmn⟩ = 0 :=
            Nat.le_antisymm (h0 ▸ hge) (Nat.zero_le _)
          refine Or.inr ⟨m, hmn, Nat.lt_succ_self m, ?_⟩
          rw [hmax, hfm0, h0]
        · exact Or.inr ⟨k, hk, Nat.lt_succ_of_lt hkm, by rw [hmax]; exact hfk⟩
    · -- m ≥ n : the slot is 0
      have hunf : fmax f (m+1) = Nat.max (fmax f m) 0 := by
        show Nat.max (fmax f m) (if h : m < n then f ⟨m, h⟩ else 0)
              = Nat.max (fmax f m) 0
        rw [dif_neg (Nat.not_lt_of_le hmn)]
      rw [hunf]
      have hmax : Nat.max (fmax f m) 0 = fmax f m := max_eq_left (Nat.zero_le _)
      rcases fmax_attained f m with h0 | ⟨k, hk, hkm, hfk⟩
      · exact Or.inl (by rw [hmax]; exact h0)
      · exact Or.inr ⟨k, hk, Nat.lt_succ_of_lt hkm, by rw [hmax]; exact hfk⟩

/-! ## Predecessor max and the fuel-bounded height

`predVals le i g k` selects `g k` when `k ≺ i` (`le k i ∧ k ≠ i`), else 0.
`heightF le f i` = longest strict chain ending at `i` using `≤ f` steps. -/

/-- For a candidate value function `g : Fin n → Nat`, restrict to strict
    predecessors of `i`: keep `g ⟨k,_⟩` if `⟨k,_⟩ ≺ i`, else `0`. -/
def predVal {n : Nat} (le : Fin n → Fin n → Bool) (i : Fin n)
    (g : Fin n → Nat) : Fin n → Nat :=
  fun k => if le k i = true ∧ k ≠ i then g k else 0

/-- `heightF le f i` = `1 + max{ heightF le (f-1) k : k ≺ i }` for `f ≥ 1`,
    `heightF le 0 i = 0`.  Fuel `f` bounds the chain length. -/
def heightF {n : Nat} (le : Fin n → Fin n → Bool) : Nat → Fin n → Nat
  | 0, _ => 0
  | f+1, i => 1 + fmax (predVal le i (fun k => heightF le f k)) n

/-- Canonical fuel at which `heightF` has stabilized (`n*n+1`, ≥ every
    stable fuel — see `heightF_stable`). -/
def stableFuel (n : Nat) : Nat := n*n + 1

/-- **The height function.**  `height i = 1 + max{ height j : j ≺ i }`, the
    longest strict chain ending at `i`, read off the stabilized fuel-fold. -/
def height {n : Nat} (le : Fin n → Fin n → Bool) (i : Fin n) : Nat :=
  heightF le (stableFuel n) i

/-! ## Data-valued argmax over the first `m` indices (choice-free)

`fmaxArg f m` returns the maximizing index `< m` (when the max is positive)
as data, mirroring `ErdosSzekeres.maxBelowArg`. -/

/-- Data-valued max attainment for `fmax`. -/
def fmaxArg {n : Nat} (f : Fin n → Nat) :
    (m : Nat) →
      (Σ' (k : Nat) (hk : k < n), k < m ∧ f ⟨k, hk⟩ = fmax f m)
        ⊕ PLift (fmax f m = 0)
  | 0 => Sum.inr (PLift.up rfl)
  | m+1 =>
    if hmn : m < n then by
      have hunf : fmax f (m+1) = Nat.max (fmax f m) (f ⟨m, hmn⟩) := by
        show Nat.max (fmax f m) (if h : m < n then f ⟨m, h⟩ else 0)
              = Nat.max (fmax f m) (f ⟨m, hmn⟩)
        rw [dif_pos hmn]
      exact
        if hlt : fmax f m < f ⟨m, hmn⟩ then
          Sum.inl ⟨m, hmn, Nat.lt_succ_self m, by
            rw [hunf, E213.Meta.Nat.AddMod213.max_comm]
            exact (max_eq_left (Nat.le_of_lt hlt)).symm⟩
        else
          have hge : f ⟨m, hmn⟩ ≤ fmax f m := Nat.le_of_not_lt hlt
          have hmax : fmax f (m+1) = fmax f m := by rw [hunf]; exact max_eq_left hge
          match fmaxArg f m with
          | Sum.inl ⟨k, hk, hkm, hfk⟩ =>
            Sum.inl ⟨k, hk, Nat.lt_succ_of_lt hkm, by rw [hmax]; exact hfk⟩
          | Sum.inr h0 =>
            Sum.inr (PLift.up (by rw [hmax]; exact h0.down))
    else by
      have hunf : fmax f (m+1) = Nat.max (fmax f m) 0 := by
        show Nat.max (fmax f m) (if h : m < n then f ⟨m, h⟩ else 0)
              = Nat.max (fmax f m) 0
        rw [dif_neg hmn]
      have hmax : fmax f (m+1) = fmax f m := by
        rw [hunf]; exact max_eq_left (Nat.zero_le _)
      exact
        match fmaxArg f m with
        | Sum.inl ⟨k, hk, hkm, hfk⟩ =>
          Sum.inl ⟨k, hk, Nat.lt_succ_of_lt hkm, by rw [hmax]; exact hfk⟩
        | Sum.inr h0 =>
          Sum.inr (PLift.up (by rw [hmax]; exact h0.down))

/-! ## Basic height facts -/

/-- Unfold one step of the height fuel. -/
theorem heightF_unfold {n : Nat} (le : Fin n → Fin n → Bool) (f : Nat) (i : Fin n) :
    heightF le (f+1) i = 1 + fmax (predVal le i (fun k => heightF le f k)) n := rfl

/-- `1 ≤ heightF le (f+1) i` always. -/
theorem one_le_heightF {n : Nat} (le : Fin n → Fin n → Bool) (f : Nat) (i : Fin n) :
    1 ≤ heightF le (f+1) i := by
  rw [heightF_unfold]; exact Nat.le_add_right 1 _

/-- `predVal le i g k = g k` when `k ≺ i`. -/
theorem predVal_pos {n : Nat} (le : Fin n → Fin n → Bool) (i : Fin n)
    (g : Fin n → Nat) {k : Fin n} (h : le k i = true ∧ k ≠ i) :
    predVal le i g k = g k := by
  show (if le k i = true ∧ k ≠ i then g k else 0) = g k
  rw [if_pos h]

/-- `predVal le i g k = 0` when `¬ (k ≺ i)`. -/
theorem predVal_zero {n : Nat} (le : Fin n → Fin n → Bool) (i : Fin n)
    (g : Fin n → Nat) {k : Fin n} (h : ¬ (le k i = true ∧ k ≠ i)) :
    predVal le i g k = 0 := by
  show (if le k i = true ∧ k ≠ i then g k else 0) = 0
  rw [if_neg h]

/-! ## Predecessor strict step (the key local monotonicity)

If `j ≺ i` then `heightF le f j < heightF le (f+1) i`: a strict predecessor
adds (at least) one to the chain. -/

/-- **Strict step across fuel.** `j ≺ i ⟹ heightF le f j < heightF le (f+1) i`. -/
theorem heightF_pred_lt {n : Nat} (le : Fin n → Fin n → Bool) (f : Nat)
    {j i : Fin n} (h : le j i = true ∧ j ≠ i) :
    heightF le f j < heightF le (f+1) i := by
  rw [heightF_unfold]
  -- predVal le i (heightF f) j = heightF f j ≤ fmax (...) n
  have hpv : predVal le i (fun k => heightF le f k) j = heightF le f j :=
    predVal_pos le i _ h
  have hle : heightF le f j
           ≤ fmax (predVal le i (fun k => heightF le f k)) n := by
    rw [← hpv]
    exact le_fmax (predVal le i (fun k => heightF le f k)) n j.val j.isLt j.isLt
  -- heightF f j ≤ M < 1 + M
  have : 1 + fmax (predVal le i (fun k => heightF le f k)) n
       = fmax (predVal le i (fun k => heightF le f k)) n + 1 := Nat.add_comm _ _
  rw [this]
  exact Nat.lt_succ_of_le hle

/-! ## Choice-free predecessor and the realized chain (bounds the height)

`predData` extracts, from `2 ≤ heightF le (f+1) i`, a strict predecessor `k ≺ i`
with `heightF le f k + 1 = heightF le (f+1) i`.  Iterating it builds a chain of
strictly-dropping fuel-heights; the heights being distinct bounds the length by `n`. -/

/-- Choice-free strict predecessor with the fuel-height dropping by exactly one. -/
def predData {n : Nat} (le : Fin n → Fin n → Bool) (f : Nat) (i : Fin n)
    (hi : 2 ≤ heightF le (f+1) i) :
    Σ' (k : Fin n), (le k i = true ∧ k ≠ i) ∧ heightF le f k + 1 = heightF le (f+1) i := by
  have hmbeq : fmax (predVal le i (fun k => heightF le f k)) n + 1 = heightF le (f+1) i := by
    rw [heightF_unfold]; exact Nat.add_comm _ 1
  have hmbpos : 1 ≤ fmax (predVal le i (fun k => heightF le f k)) n := by
    have h2 : 2 ≤ fmax (predVal le i (fun k => heightF le f k)) n + 1 := hmbeq ▸ hi
    exact Nat.le_of_succ_le_succ h2
  match fmaxArg (predVal le i (fun k => heightF le f k)) n with
  | Sum.inr h0 =>
    exact absurd (by rw [← h0.down]; exact hmbpos : (1:Nat) ≤ 0) (Nat.not_succ_le_zero 0)
  | Sum.inl ⟨kv, hkv, _, hfk⟩ =>
    -- predVal at ⟨kv,hkv⟩ = fmax ≥ 1, so the `if` is the true branch
    have hge1 : 1 ≤ predVal le i (fun k => heightF le f k) ⟨kv, hkv⟩ := by
      rw [hfk]; exact hmbpos
    refine ⟨⟨kv, hkv⟩, ?_, ?_⟩
    · -- the predicate must hold else predVal = 0
      by_cases hp : le ⟨kv, hkv⟩ i = true ∧ ⟨kv, hkv⟩ ≠ i
      · exact hp
      · exfalso
        have h0 : predVal le i (fun k => heightF le f k) ⟨kv, hkv⟩ = 0 :=
          predVal_zero le i _ hp
        exact absurd (by rw [← h0]; exact hge1 : (1:Nat) ≤ 0) (Nat.not_succ_le_zero 0)
    · -- heightF f ⟨kv,hkv⟩ = fmax, and fmax + 1 = heightF (f+1) i
      by_cases hp : le ⟨kv, hkv⟩ i = true ∧ ⟨kv, hkv⟩ ≠ i
      · have hpv : predVal le i (fun k => heightF le f k) ⟨kv, hkv⟩
                 = heightF le f ⟨kv, hkv⟩ := predVal_pos le i _ hp
        have : heightF le f ⟨kv, hkv⟩
             = fmax (predVal le i (fun k => heightF le f k)) n := by
          rw [← hpv]; exact hfk
        rw [this]; exact hmbeq
      · exfalso
        have h0 : predVal le i (fun k => heightF le f k) ⟨kv, hkv⟩ = 0 :=
          predVal_zero le i _ hp
        exact absurd (by rw [← h0]; exact hge1 : (1:Nat) ≤ 0) (Nat.not_succ_le_zero 0)

/-! ### Chain from `i` down at fixed starting fuel `F`

`chain F i t` walks `t` predecessor steps from `i`, the fuel dropping `F → F-t`.
Invariant: `heightF le (F-t) (chain t) = heightF le F i - t` for `t < heightF le F i`. -/

/-- Total predecessor step at fuel `g` (`g` is the *target* fuel `F-t`,
    so the source height lives at `g+1`'s shape via `g = (g-1)+1` when `g ≥ 1`). -/
def chainStep {n : Nat} (le : Fin n → Fin n → Bool) (g : Nat) (x : Fin n) : Fin n :=
  match g with
  | 0 => x
  | g'+1 => if h : 2 ≤ heightF le (g'+1) x then (predData le g' x h).1 else x

/-- `chain F i t` = index after `t` predecessor steps from `i`. -/
def chain {n : Nat} (le : Fin n → Fin n → Bool) (F : Nat) (i : Fin n) : Nat → Fin n
  | 0 => i
  | t+1 => chainStep le (F - t) (chain le F i t)

/-- Height invariant along the chain: after `t < heightF F i` steps the height
    (at fuel `F-t`) is `heightF F i - t`. -/
theorem chain_height {n : Nat} (le : Fin n → Fin n → Bool) (F : Nat) (i : Fin n) :
    ∀ t, t < heightF le F i → heightF le (F - t) (chain le F i t) = heightF le F i - t
  | 0, _ => by show heightF le (F - 0) i = heightF le F i - 0; rw [Nat.sub_zero, Nat.sub_zero]
  | t+1, ht => by
    have htlt : t < heightF le F i := Nat.lt_of_succ_lt ht
    have ih : heightF le (F - t) (chain le F i t) = heightF le F i - t :=
      chain_height le F i t htlt
    -- heightF F i - t ≥ 2 since t+1 < heightF F i
    have hge2 : 2 ≤ heightF le (F - t) (chain le F i t) := by
      rw [ih]
      exact E213.Tactic.NatHelper.le_sub_of_add_le (by
        rw [Nat.add_comm]; exact (ht : t + 2 ≤ heightF le F i))
    -- so heightF (F-t) (chain t) ≥ 2 > 0 ⟹ F - t ≥ 1
    have hFt1 : 1 ≤ F - t := by
      rcases Nat.eq_zero_or_pos (F - t) with h0 | hpos
      · -- F - t = 0 ⟹ heightF 0 _ = 0, contradicting ≥ 2
        exfalso
        have : heightF le (F - t) (chain le F i t) = 0 := by rw [h0]; rfl
        rw [this] at hge2; exact absurd hge2 (by decide)
      · exact hpos
    -- write F - t = (F-t-1) + 1
    obtain ⟨g', hg'⟩ : ∃ g', F - t = g' + 1 :=
      ⟨F - t - 1, by rw [E213.Tactic.NatHelper.sub_add_cancel hFt1]⟩
    -- F - (t+1) = (F-t) - 1 = g'  (Nat.sub_succ: `· - (t+1) ≡ pred (· - t) ≡ · - t - 1`)
    have hFt1eq : F - (t+1) = g' := by
      show (F - t) - 1 = g'; rw [hg']; rfl
    -- height at fuel (g'+1)
    have hge2' : 2 ≤ heightF le (g'+1) (chain le F i t) := hg' ▸ hge2
    -- chain (t+1) = chainStep (F-t) (chain t) = predData ... .1
    have hstep : chain le F i (t+1) = (predData le g' (chain le F i t) hge2').1 := by
      show chainStep le (F - t) (chain le F i t) = _
      rw [hg']
      show (if h : 2 ≤ heightF le (g'+1) (chain le F i t) then (predData le g' (chain le F i t) h).1 else _) = _
      rw [dif_pos hge2']
    -- predData: heightF g' k + 1 = heightF (g'+1) (chain t) = heightF (F-t) (chain t) = heightF F i - t
    have hpd := (predData le g' (chain le F i t) hge2').2.2
    have hval : heightF le g' (predData le g' (chain le F i t) hge2').1 + 1
              = heightF le F i - t := by
      rw [hpd, ← hg', ih]
    show heightF le (F - (t+1)) (chain le F i (t+1)) = heightF le F i - (t+1)
    rw [hFt1eq, hstep]
    -- heightF g' k = (heightF F i - t) - 1 = heightF F i - (t+1)
    have : heightF le g' (predData le g' (chain le F i t) hge2').1
         = heightF le F i - t - 1 := by
      rw [← hval]
      exact (E213.Tactic.NatHelper.add_sub_cancel_right _ 1).symm
    rw [this]
    show heightF le F i - t - 1 = heightF le F i - (t + 1)
    rfl

/-- One chain step is a strict predecessor: `chain (t+1) ≺ chain t`. -/
theorem chain_pred {n : Nat} (le : Fin n → Fin n → Bool) (F : Nat) (i : Fin n)
    (t : Nat) (ht : t + 1 < heightF le F i) :
    le (chain le F i (t+1)) (chain le F i t) = true ∧ chain le F i (t+1) ≠ chain le F i t := by
  have htlt : t < heightF le F i := Nat.lt_of_succ_lt ht
  have hh : heightF le (F - t) (chain le F i t) = heightF le F i - t :=
    chain_height le F i t htlt
  have hge2 : 2 ≤ heightF le (F - t) (chain le F i t) := by
    rw [hh]
    exact E213.Tactic.NatHelper.le_sub_of_add_le (by
      rw [Nat.add_comm]; exact (ht : t + 2 ≤ heightF le F i))
  have hFt1 : 1 ≤ F - t := by
    rcases Nat.eq_zero_or_pos (F - t) with h0 | hpos
    · exfalso
      have : heightF le (F - t) (chain le F i t) = 0 := by rw [h0]; rfl
      rw [this] at hge2; exact absurd hge2 (by decide)
    · exact hpos
  obtain ⟨g', hg'⟩ : ∃ g', F - t = g' + 1 :=
    ⟨F - t - 1, by rw [E213.Tactic.NatHelper.sub_add_cancel hFt1]⟩
  have hge2' : 2 ≤ heightF le (g'+1) (chain le F i t) := hg' ▸ hge2
  have hstep : chain le F i (t+1) = (predData le g' (chain le F i t) hge2').1 := by
    show chainStep le (F - t) (chain le F i t) = _
    rw [hg']
    show (if h : 2 ≤ heightF le (g'+1) (chain le F i t) then (predData le g' (chain le F i t) h).1 else _) = _
    rw [dif_pos hge2']
  have hpd := (predData le g' (chain le F i t) hge2').2.1
  rw [hstep]; exact hpd

/-- Any later chain element is a strict predecessor of an earlier one:
    `s < t < heightF F i ⟹ chain t ≺ chain s`. -/
theorem chain_pred_lt {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    (F : Nat) (i : Fin n) :
    ∀ (d s : Nat), s + (d+1) < heightF le F i →
      le (chain le F i (s + (d+1))) (chain le F i s) = true
      ∧ chain le F i (s + (d+1)) ≠ chain le F i s
  | 0, s, hs => by
    have : s + 1 < heightF le F i := hs
    exact chain_pred le F i s this
  | d+1, s, hs => by
    -- step s → s+1, then chain_pred_lt from s+1 by d+1
    have hs1 : s + 1 < heightF le F i :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) s) hs
    have hstep := chain_pred le F i s hs1
    have hassoc : s + (d + 2) = (s + 1) + (d + 1) := by
      rw [Nat.add_assoc s 1 (d+1)]
      have : (1 : Nat) + (d + 1) = d + 2 := by rw [Nat.add_comm 1 (d+1)]
      rw [this]
    have hrec : (s+1) + (d+1) < heightF le F i := by rw [← hassoc]; exact hs
    have hanti := chain_pred_lt le hp F i d (s+1) hrec
    rw [hassoc]
    refine ⟨hp.trans _ _ _ hanti.1 hstep.1, ?_⟩
    -- chain ((s+1)+(d+1)) ≠ chain s :  else le (chain s) (chain (s+1)) too ⟹ s+1 = s via antisymm
    intro heq
    -- from heq: chain (s+1+(d+1)) = chain s, and le (chain(s+1+(d+1))) (chain(s+1)) = true (hanti.1)
    -- so le (chain s) (chain (s+1)) = true; with le (chain(s+1)) (chain s) (hstep.1) ⟹ chain s = chain(s+1)
    have hle1 : le (chain le F i s) (chain le F i (s+1)) = true := heq ▸ hanti.1
    have : chain le F i s = chain le F i (s+1) := hp.antisymm _ _ hle1 hstep.1
    exact hstep.2 this.symm

/-- Distinct chain indices give distinct elements (on `[0, heightF F i)`). -/
theorem chain_inj {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    (F : Nat) (i : Fin n) {s t : Nat} (hs : s < heightF le F i) (ht : t < heightF le F i)
    (hst : s ≠ t) : chain le F i s ≠ chain le F i t := by
  rcases Nat.lt_or_ge s t with hlt | hge
  · -- s < t : chain t ≺ chain s
    obtain ⟨d, hd⟩ : ∃ d, t = s + (d+1) := by
      obtain ⟨c, hc⟩ := Nat.le.dest (Nat.succ_le_of_lt hlt)
      refine ⟨c, ?_⟩
      rw [← hc]
      show s + 1 + c = s + (c + 1)
      rw [Nat.add_assoc, Nat.add_comm 1 c]
    have : chain le F i (s + (d+1)) ≠ chain le F i s :=
      (chain_pred_lt le hp F i d s (hd ▸ ht)).2
    rw [hd]; exact fun e => this e.symm
  · have hlt : t < s := Nat.lt_of_le_of_ne hge (fun e => hst e.symm)
    obtain ⟨d, hd⟩ : ∃ d, s = t + (d+1) := by
      obtain ⟨c, hc⟩ := Nat.le.dest (Nat.succ_le_of_lt hlt)
      refine ⟨c, ?_⟩
      rw [← hc]
      show t + 1 + c = t + (c + 1)
      rw [Nat.add_assoc, Nat.add_comm 1 c]
    have : chain le F i (t + (d+1)) ≠ chain le F i t :=
      (chain_pred_lt le hp F i d t (hd ▸ hs)).2
    rw [hd]; exact this

/-! ### The height bound: every fuel-height is `≤ n` -/

/-- **Height bound.**  In an `n`-element poset, every fuel-height is `≤ n`. -/
theorem heightF_le_card {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    (F : Nat) (i : Fin n) : heightF le F i ≤ n := by
  -- else heightF F i > n gives an injection Fin (heightF F i) → Fin n, pigeonhole ⟹ collision,
  -- contradicting chain_inj.
  rcases Nat.lt_or_ge n (heightF le F i) with hlt | hge
  · exfalso
    let g : Fin (heightF le F i) → Fin n := fun t => chain le F i t.val
    obtain ⟨s, t, hst, hgst⟩ :=
      E213.Lib.Math.Combinatorics.Pigeonhole.exists_collision_lt hlt g
    have hsne : s.val ≠ t.val := fun e => hst (Fin.ext e)
    exact chain_inj le hp F i s.isLt t.isLt hsne hgst
  · exact hge

/-! ## Fuel monotonicity and the sum potential (stabilization)

`heightF` is monotone in fuel.  The sum `fsum (heightF le f) n` is monotone and
bounded by `n*n`, so it stabilizes: at the stable fuel every element's height is
fixed, hence `heightF le (f+1) = heightF le f`. -/

/-- ∅-axiom `max ≤`: `a ≤ c → b ≤ c → max a b ≤ c`. -/
theorem max_le_of {a b c : Nat} (hac : a ≤ c) (hbc : b ≤ c) : Nat.max a b ≤ c :=
  match Nat.le_total a b with
  | Or.inl hab => Nat.le_trans (Nat.le_of_eq (Nat.max_eq_right hab)) hbc
  | Or.inr hba => Nat.le_trans (Nat.le_of_eq (max_eq_left hba)) hac

/-- ∅-axiom `max` monotonicity: `a ≤ c → b ≤ d → max a b ≤ max c d`. -/
theorem max_le_max {a b c d : Nat} (hac : a ≤ c) (hbd : b ≤ d) :
    Nat.max a b ≤ Nat.max c d :=
  max_le_of (Nat.le_trans hac (le_max_left c d))
            (Nat.le_trans hbd (le_max_right c d))

/-- `fmax` is monotone in its function argument. -/
theorem fmax_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ k, f k ≤ g k) :
    ∀ m, fmax f m ≤ fmax g m
  | 0 => Nat.le_refl 0
  | m+1 => by
    show Nat.max (fmax f m) (if hm : m < n then f ⟨m, hm⟩ else 0)
       ≤ Nat.max (fmax g m) (if hm : m < n then g ⟨m, hm⟩ else 0)
    rcases Nat.lt_or_ge m n with hmn | hmn
    · rw [dif_pos hmn, dif_pos hmn]
      exact max_le_max (fmax_mono h m) (h ⟨m, hmn⟩)
    · rw [dif_neg (Nat.not_lt_of_le hmn), dif_neg (Nat.not_lt_of_le hmn)]
      exact max_le_max (fmax_mono h m) (Nat.le_refl 0)

/-- **Fuel monotonicity.** `heightF le f i ≤ heightF le (f+1) i`. -/
theorem heightF_mono {n : Nat} (le : Fin n → Fin n → Bool) :
    ∀ (f : Nat) (i : Fin n), heightF le f i ≤ heightF le (f+1) i
  | 0, i => Nat.zero_le _
  | f+1, i => by
    rw [heightF_unfold, heightF_unfold]
    apply Nat.add_le_add_left
    apply fmax_mono
    intro k
    -- predVal le i (heightF f) k ≤ predVal le i (heightF (f+1)) k
    by_cases hp : le k i = true ∧ k ≠ i
    · rw [predVal_pos le i _ hp, predVal_pos le i _ hp]
      exact heightF_mono le f k
    · rw [predVal_zero le i _ hp, predVal_zero le i _ hp]
      exact Nat.le_refl 0

/-- If two value functions agree pointwise, their `fmax` agree (∅). -/
theorem fmax_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ k, f k = g k) (m : Nat) :
    fmax f m = fmax g m :=
  Nat.le_antisymm (fmax_mono (fun k => Nat.le_of_eq (h k)) m)
                  (fmax_mono (fun k => Nat.le_of_eq (h k).symm) m)

/-- **Step lemma.** If all heights at fuel `f` already equal those at `f+1`,
    then the same holds at `f+1` vs `f+2`. -/
theorem heightF_step {n : Nat} (le : Fin n → Fin n → Bool) (f : Nat)
    (h : ∀ k, heightF le f k = heightF le (f+1) k) (i : Fin n) :
    heightF le (f+1) i = heightF le (f+2) i := by
  rw [heightF_unfold, heightF_unfold]
  apply congrArg (1 + ·)
  apply fmax_congr
  intro k
  by_cases hp : le k i = true ∧ k ≠ i
  · rw [predVal_pos le i _ hp, predVal_pos le i _ hp]; exact h k
  · rw [predVal_zero le i _ hp, predVal_zero le i _ hp]

/-- Upward closure: once stable at `f₀`, stable at every `f ≥ f₀` (one step form). -/
theorem heightF_stable_from {n : Nat} (le : Fin n → Fin n → Bool) (f₀ : Nat)
    (h0 : ∀ k, heightF le f₀ k = heightF le (f₀+1) k) :
    ∀ (d : Nat) (i : Fin n), heightF le (f₀ + d) i = heightF le (f₀ + d + 1) i
  | 0, i => h0 i
  | d+1, i => by
    have ih : ∀ k, heightF le (f₀ + d) k = heightF le (f₀ + d + 1) k :=
      fun k => heightF_stable_from le f₀ h0 d k
    -- f₀+(d+1) ≡ (f₀+d)+1 and f₀+(d+1)+1 ≡ (f₀+d)+2 definitionally
    exact heightF_step le (f₀ + d) ih i

/-! ### Sum over the first `m` indices (the potential) -/

/-- `fsum f m = Σ_{k<m} f ⟨k,·⟩`, empty = 0. -/
def fsum {n : Nat} (f : Fin n → Nat) : Nat → Nat
  | 0 => 0
  | m+1 => fsum f m + (if h : m < n then f ⟨m, h⟩ else 0)

/-- `fsum` is monotone under a pointwise `≤`. -/
theorem fsum_mono {n : Nat} {f g : Fin n → Nat} (h : ∀ k, f k ≤ g k) :
    ∀ m, fsum f m ≤ fsum g m
  | 0 => Nat.le_refl 0
  | m+1 => by
    show fsum f m + (if hm : m < n then f ⟨m, hm⟩ else 0)
       ≤ fsum g m + (if hm : m < n then g ⟨m, hm⟩ else 0)
    rcases Nat.lt_or_ge m n with hmn | hmn
    · rw [dif_pos hmn, dif_pos hmn]
      exact Nat.add_le_add (fsum_mono h m) (h ⟨m, hmn⟩)
    · rw [dif_neg (Nat.not_lt_of_le hmn), dif_neg (Nat.not_lt_of_le hmn)]
      exact Nat.add_le_add (fsum_mono h m) (Nat.le_refl 0)

/-- Strict sum bump: pointwise `≤` plus a strict in-range entry `< m` ⟹ strict sum. -/
theorem fsum_lt {n : Nat} {f g : Fin n → Nat} (h : ∀ k, f k ≤ g k)
    {k0 : Nat} (hk0 : k0 < n) (hstrict : f ⟨k0, hk0⟩ < g ⟨k0, hk0⟩) :
    ∀ m, k0 < m → fsum f m < fsum g m
  | 0, hlt => absurd hlt (Nat.not_lt_zero _)
  | m+1, hlt => by
    show fsum f m + (if hm : m < n then f ⟨m, hm⟩ else 0)
       < fsum g m + (if hm : m < n then g ⟨m, hm⟩ else 0)
    rcases Nat.lt_or_ge k0 m with hk0m | hk0m
    · -- strict already in the prefix
      have hpre : fsum f m < fsum g m := fsum_lt h hk0 hstrict m hk0m
      rcases Nat.lt_or_ge m n with hmn | hmn
      · rw [dif_pos hmn, dif_pos hmn]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hpre _)
          (Nat.add_le_add_left (h ⟨m, hmn⟩) _)
      · rw [dif_neg (Nat.not_lt_of_le hmn), dif_neg (Nat.not_lt_of_le hmn)]
        exact Nat.add_lt_add_right hpre _
    · -- k0 = m : strict at the last slot
      have hk0eq : k0 = m := Nat.le_antisymm (Nat.le_of_lt_succ hlt) hk0m
      have hmn : m < n := hk0eq ▸ hk0
      rw [dif_pos hmn, dif_pos hmn]
      have hpre : fsum f m ≤ fsum g m := fsum_mono h m
      have hslot : f ⟨m, hmn⟩ < g ⟨m, hmn⟩ := by
        have : (⟨k0, hk0⟩ : Fin n) = ⟨m, hmn⟩ := Fin.ext hk0eq
        rw [← this]; exact hstrict
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_right hpre _)
        (Nat.add_lt_add_left hslot _)

/-- `fsum (heightF le f) n ≤ n * n` (each of `n` entries is `≤ n`). -/
theorem fsum_heightF_le {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    (f : Nat) : ∀ m, m ≤ n → fsum (fun k => heightF le f k) m ≤ m * n
  | 0, _ => Nat.zero_le _
  | m+1, hm => by
    have hmn : m < n := hm
    show fsum (fun k => heightF le f k) m
          + (if h : m < n then heightF le f ⟨m, h⟩ else 0)
       ≤ (m+1) * n
    rw [dif_pos hmn]
    have hpre : fsum (fun k => heightF le f k) m ≤ m * n :=
      fsum_heightF_le le hp f m (Nat.le_of_lt hmn)
    have hentry : heightF le f ⟨m, hmn⟩ ≤ n := heightF_le_card le hp f ⟨m, hmn⟩
    have : (m+1) * n = m * n + n := by rw [Nat.succ_mul]
    rw [this]
    exact Nat.add_le_add hpre hentry

/-- Bounded scan: either an element whose height strictly grows from fuel `f`
    to `f+1` (within the first `m`), or a proof all first-`m` heights are stable. -/
theorem findGrow {n : Nat} (le : Fin n → Fin n → Bool) (f : Nat) :
    ∀ (m : Nat), m ≤ n →
      (∃ k : Fin n, heightF le f k < heightF le (f+1) k)
      ∨ (∀ k : Fin n, k.val < m → heightF le f k = heightF le (f+1) k)
  | 0, _ => Or.inr (fun k hk => absurd hk (Nat.not_lt_zero _))
  | m+1, hm => by
    have hmn : m < n := hm
    rcases findGrow le f m (Nat.le_of_lt hmn) with hgrow | hball
    · exact Or.inl hgrow
    · -- decide at p = ⟨m, hmn⟩
      let p : Fin n := ⟨m, hmn⟩
      rcases Nat.lt_or_ge (heightF le f p) (heightF le (f+1) p) with hlt | hge
      · exact Or.inl ⟨p, hlt⟩
      · -- heightF f p ≥ heightF (f+1) p, with mono ⟹ equal ⟹ extend hball
        have heq : heightF le f p = heightF le (f+1) p :=
          Nat.le_antisymm (heightF_mono le f p) hge
        refine Or.inr (fun k hk => ?_)
        rcases Nat.lt_or_ge k.val m with hkm | hkm
        · exact hball k hkm
        · have hkeq : k.val = m := Nat.le_antisymm (Nat.le_of_lt_succ hk) hkm
          have : k = p := Fin.ext hkeq
          rw [this]; exact heq

/-- If every fuel `f < c` strictly grows some element, the sum potential at
    fuel `c` is `≥ c`. -/
theorem sum_ge_of_grow {n : Nat} (le : Fin n → Fin n → Bool) :
    ∀ c, (∀ f, f < c → ∃ k : Fin n, heightF le f k < heightF le (f+1) k) →
      c ≤ fsum (fun k => heightF le c k) n
  | 0, _ => Nat.zero_le _
  | c+1, grow => by
    have ih : c ≤ fsum (fun k => heightF le c k) n :=
      sum_ge_of_grow le c (fun f hf => grow f (Nat.lt_succ_of_lt hf))
    obtain ⟨k, hk⟩ := grow c (Nat.lt_succ_self c)
    have hmono : ∀ j : Fin n, heightF le c j ≤ heightF le (c+1) j :=
      fun j => heightF_mono le c j
    have hstrict : fsum (fun j => heightF le c j) n < fsum (fun j => heightF le (c+1) j) n :=
      fsum_lt hmono k.isLt hk n k.isLt
    exact Nat.le_trans (Nat.succ_le_succ ih) hstrict

/-- Scan fuels `0..b` for a stable fuel `f₀ ≤ b`, else every scanned fuel grows. -/
theorem scanFuel {n : Nat} (le : Fin n → Fin n → Bool) :
    ∀ (b : Nat),
      (∃ f₀, f₀ ≤ b ∧ ∀ k : Fin n, heightF le f₀ k = heightF le (f₀+1) k)
      ∨ (∀ f, f < b → ∃ k : Fin n, heightF le f k < heightF le (f+1) k)
  | 0 => Or.inr (fun f hf => absurd hf (Nat.not_lt_zero _))
  | b+1 => by
    rcases scanFuel le b with hstab | hall
    · obtain ⟨f₀, hf₀, hstabk⟩ := hstab
      exact Or.inl ⟨f₀, Nat.le_succ_of_le hf₀, hstabk⟩
    · -- decide fuel b: stable or grows
      rcases findGrow le b n (Nat.le_refl n) with hgrow | hball
      · -- some element grows at fuel b
        refine Or.inr (fun f hf => ?_)
        rcases Nat.lt_or_ge f b with hfb | hfb
        · exact hall f hfb
        · have hfeq : f = b := Nat.le_antisymm (Nat.le_of_lt_succ hf) hfb
          rw [hfeq]; exact hgrow
      · -- fuel b stable (all elements equal, since k.val < n always)
        exact Or.inl ⟨b, Nat.le_succ b, fun k => hball k k.isLt⟩

/-- **Stabilization exists.**  Some fuel `f₀ ≤ n*n+1` is stable: heights at `f₀`
    equal heights at `f₀+1` for every element.  (Else the sum potential, bounded
    by `n*n`, would exceed `n*n+1`.) -/
theorem stable_exists {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le) :
    ∃ f₀, f₀ ≤ n*n+1 ∧ ∀ k : Fin n, heightF le f₀ k = heightF le (f₀+1) k := by
  rcases scanFuel le (n*n+1) with hstab | hall
  · exact hstab
  · exfalso
    have hge : n*n+1 ≤ fsum (fun k => heightF le (n*n+1) k) n :=
      sum_ge_of_grow le (n*n+1) hall
    have hle : fsum (fun k => heightF le (n*n+1) k) n ≤ n*n :=
      fsum_heightF_le le hp (n*n+1) n (Nat.le_refl n)
    exact absurd (Nat.le_trans hge hle) (Nat.not_succ_le_self (n*n))

/-! ## The stable height and its strict monotonicity

`height i := heightF le (n*n+1) i`.  Fuel `n*n+1` is `≥` any stable fuel
(`stable_exists`), so `heightF` is constant from there on. -/

/-- `heightF` is constant at and beyond the canonical stable fuel. -/
theorem heightF_stable {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le) :
    ∀ (d : Nat) (i : Fin n),
      heightF le (stableFuel n) i = heightF le (stableFuel n + d) i := by
  obtain ⟨f₀, hf₀, hstab⟩ := stable_exists le hp
  -- f₀ ≤ n*n+1 = stableFuel n; stable_from gives stability for all fuels ≥ f₀
  obtain ⟨e, he⟩ : ∃ e, stableFuel n = f₀ + e :=
    ⟨stableFuel n - f₀, by
      show stableFuel n = f₀ + (stableFuel n - f₀)
      rw [Nat.add_comm]
      exact (E213.Tactic.NatHelper.sub_add_cancel hf₀).symm⟩
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    -- heightF (stableFuel) i = heightF (stableFuel + d) i  (ih)
    --                        = heightF (stableFuel + d + 1) i  (stable step, since stableFuel+d ≥ f₀)
    have hstep : heightF le (stableFuel n + d) i = heightF le (stableFuel n + d + 1) i := by
      -- stableFuel + d = f₀ + (e + d)
      have hsplit : stableFuel n + d = f₀ + (e + d) := by
        rw [he, Nat.add_assoc]
      rw [hsplit]
      exact heightF_stable_from le f₀ hstab (e + d) i
    have : heightF le (stableFuel n) i = heightF le (stableFuel n + d + 1) i := by
      rw [ih i, hstep]
    -- stableFuel + (d+1) = stableFuel + d + 1
    show heightF le (stableFuel n) i = heightF le (stableFuel n + (d+1)) i
    exact this

/-- **Key strict monotonicity.** `j ≺ i ⟹ height j < height i`. -/
theorem height_lt_of_lt {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    {j i : Fin n} (h : le j i = true ∧ j ≠ i) : height le j < height le i := by
  -- height j = heightF (stableFuel) j < heightF (stableFuel+1) i = heightF (stableFuel) i = height i
  have hpred : heightF le (stableFuel n) j < heightF le (stableFuel n + 1) i :=
    heightF_pred_lt le (stableFuel n) h
  have hstab : heightF le (stableFuel n) i = heightF le (stableFuel n + 1) i :=
    heightF_stable le hp 1 i
  show heightF le (stableFuel n) j < heightF le (stableFuel n) i
  rw [hstab]; exact hpred

/-- `1 ≤ height le i` always (the singleton chain `{i}`). -/
theorem one_le_height {n : Nat} (le : Fin n → Fin n → Bool) (i : Fin n) :
    1 ≤ height le i := by
  show 1 ≤ heightF le (n*n+1) i
  exact one_le_heightF le (n*n) i

/-- `height le i ≤ n` always (chains have `≤ n` distinct elements). -/
theorem height_le_card {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    (i : Fin n) : height le i ≤ n :=
  heightF_le_card le hp (stableFuel n) i

/-! ## Mirsky: equal-height antichain + the partition into `H` antichains -/

/-- **(★) Equal heights ⟹ incomparable.**  Each height-level is an antichain:
    if `height i = height j` and `i ≠ j`, then neither `i ≺ j` nor `j ≺ i`.
    (A strict comparison would force unequal heights via `height_lt_of_lt`.) -/
theorem equal_height_antichain {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le)
    {i j : Fin n} (hheq : height le i = height le j) (hne : i ≠ j) :
    ¬ (le i j = true ∧ i ≠ j) ∧ ¬ (le j i = true ∧ j ≠ i) := by
  refine ⟨?_, ?_⟩
  · intro hij
    -- i ≺ j ⟹ height i < height j, contradicting equality
    have : height le i < height le j := height_lt_of_lt le hp hij
    exact Nat.lt_irrefl _ (hheq ▸ this)
  · intro hji
    have : height le j < height le i := height_lt_of_lt le hp hji
    exact Nat.lt_irrefl _ (hheq.symm ▸ this)

/-- **(★★) Mirsky's theorem.**  The computed height maps `Fin n` into `[1, H]`
    with `H = n`, and every height-level is an antichain — i.e. the poset is
    partitioned into `H` antichains, the level sets `height⁻¹(k)`.

    (`H = n` is the loose bound; the tight `H = longest chain length` is realized
    by the height-gradient chain — see `chain` / `chain_height` / `heightF_le_card`,
    which is exactly what forces `H ≤ n`.) -/
theorem mirsky {n : Nat} (le : Fin n → Fin n → Bool) (hp : IsPoset n le) :
    ∃ H, (∀ i, 1 ≤ height le i ∧ height le i ≤ H)
       ∧ (∀ i j, height le i = height le j → i ≠ j →
            ¬ (le i j = true ∧ i ≠ j) ∧ ¬ (le j i = true ∧ j ≠ i)) := by
  refine ⟨n, ?_, ?_⟩
  · exact fun i => ⟨one_le_height le i, height_le_card le hp i⟩
  · exact fun i j hheq hne => equal_height_antichain le hp hheq hne

/-! ## Smoke tests (concrete small posets, computed heights by `decide`/`rfl`) -/

/-- The 2-chain `0 ≤ 1` on `Fin 2` (`le a b := a.val ≤ b.val`). -/
def le2chain : Fin 2 → Fin 2 → Bool := fun a b => decide (a.val ≤ b.val)

/-- Heights of the 2-chain: bottom `0` has height `1`, top `1` has height `2`. -/
example : height le2chain ⟨0, by decide⟩ = 1 := by decide
example : height le2chain ⟨1, by decide⟩ = 2 := by decide

/-- The longest chain length (max height) of the 2-chain is `2`. -/
example : Nat.max (height le2chain ⟨0, by decide⟩) (height le2chain ⟨1, by decide⟩) = 2 := by
  decide

/-- The 2-element antichain (`le a b := a = b`) on `Fin 2`. -/
def le2anti : Fin 2 → Fin 2 → Bool := fun a b => decide (a = b)

/-- Both elements of the antichain have height `1` (no strict predecessors). -/
example : height le2anti ⟨0, by decide⟩ = 1 := by decide
example : height le2anti ⟨1, by decide⟩ = 1 := by decide

/-- Equal heights in the antichain ⟹ incomparable (the `equal_height_antichain`
    conclusion, here verified concretely). -/
example : ¬ (le2anti ⟨0, by decide⟩ ⟨1, by decide⟩ = true ∧
              (⟨0, by decide⟩ : Fin 2) ≠ ⟨1, by decide⟩)
        ∧ ¬ (le2anti ⟨1, by decide⟩ ⟨0, by decide⟩ = true ∧
              (⟨1, by decide⟩ : Fin 2) ≠ ⟨0, by decide⟩) := by decide

end E213.Lib.Math.Combinatorics.MirskyTheorem
