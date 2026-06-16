import E213.Lib.Math.Logic.Omniscience
import E213.Lib.Math.Logic.Pi01Decision

/-!
# Binary Bolzano–Weierstrass calibrated against LPO / LLPO

A vein-C *calibration*: "every bounded (binary) sequence has a convergent
(eventually-constant-valued) subsequence" is not an unconditional ∅-axiom
theorem — extracting the subsequence requires deciding "`true` occurs unboundedly
often" (Π⁰₂), strictly above the corpus ledger's LPO. The honest content is the
calibration: `lpo_of_bw` (binary BW ⟹ LPO, the strongest base rung) plus the
constructive cores (`subseq_of_unbounded_true` / `subseq_of_eventually_false`,
fully ∅-axiom once the witness is supplied as data). The non-constructivity is
named and measured, not removed.
-/

namespace E213.Lib.Math.Logic.BolzanoWeierstrass

open E213.Lib.Math.Logic

/-- Constant-subsequence existence for a `{0,1}`-sequence: a strictly-increasing index
    map onto a single value `v` — the binary Bolzano–Weierstrass conclusion. -/
def HasConstSubseq (a : Nat → Bool) : Prop :=
  ∃ v : Bool, ∃ g : Nat → Nat, (∀ i j, i < j → g i < g j) ∧ (∀ k, a (g k) = v)

/-! ## Linear least-witness search (pure, no `Nat.find`)

`findFrom a m k` scans the `k` indices `m, m+1, …, m+k-1` and returns the first with
`a = true`, or `m + k` if none. -/

def findFrom (a : Nat → Bool) (m : Nat) : Nat → Nat
  | 0     => m
  | k + 1 => match a m with
    | true  => m
    | false => findFrom a (m + 1) k

/-- Unfolding at a successor when the head is `true`. -/
theorem findFrom_succ_true (a : Nat → Bool) (m k : Nat) (h : a m = true) :
    findFrom a m (k + 1) = m := by
  show (match a m with | true => m | false => findFrom a (m + 1) k) = m
  rw [h]

/-- Unfolding at a successor when the head is `false`. -/
theorem findFrom_succ_false (a : Nat → Bool) (m k : Nat) (h : a m = false) :
    findFrom a m (k + 1) = findFrom a (m + 1) k := by
  show (match a m with | true => m | false => findFrom a (m + 1) k) = findFrom a (m + 1) k
  rw [h]

/-- The search result is at least the start. -/
theorem findFrom_ge (a : Nat → Bool) : ∀ k m, m ≤ findFrom a m k
  | 0,     m => Nat.le_refl m
  | k + 1, m => by
    cases ham : a m with
    | true  => rw [findFrom_succ_true a m k ham]; exact Nat.le_refl m
    | false =>
      rw [findFrom_succ_false a m k ham]
      exact Nat.le_trans (Nat.le_succ m) (findFrom_ge a k (m + 1))

/-- **Search succeeds.**  If some index `j` in `[m, m+k)` has `a j = true`, the search
    lands on a `true` (and stays `< m+k`).  Stated jointly so the recursion carries both
    facts. -/
theorem findFrom_succeeds (a : Nat → Bool) :
    ∀ k m j, m ≤ j → j < m + k → a j = true →
      a (findFrom a m k) = true ∧ findFrom a m k < m + k
  | 0,     m, j, hmj, hjk, _ => by
    exact absurd hjk (Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_eq (Nat.add_zero m).symm) hmj))
  | k + 1, m, j, hmj, hjk, haj => by
    cases ham : a m with
    | true =>
      rw [findFrom_succ_true a m k ham]
      exact ⟨ham, Nat.lt_add_of_pos_right (Nat.succ_pos k)⟩
    | false =>
      -- m is false, so j ≠ m, hence m+1 ≤ j
      have hjm : m + 1 ≤ j := by
        rcases Nat.lt_or_ge m j with h | h
        · exact h
        · have hjeq : j = m := Nat.le_antisymm (Nat.le_of_lt_succ (Nat.lt_succ_of_le h)) hmj
          rw [hjeq] at haj
          exact absurd (haj.symm.trans ham) (Bool.noConfusion)
      have hjk' : j < (m + 1) + k := by
        have he : m + (k + 1) = (m + 1) + k := by rw [Nat.add_succ, Nat.succ_add]
        rw [he] at hjk; exact hjk
      have ih := findFrom_succeeds a k (m + 1) j hjm hjk' haj
      rw [findFrom_succ_false a m k ham]
      refine ⟨ih.1, ?_⟩
      have he : (m + 1) + k = m + (k + 1) := by rw [Nat.succ_add, Nat.add_succ]
      rw [he] at ih
      exact ih.2

/-! ## Constructive cores (no omniscience): each cofinal value yields a subsequence -/

/-- **Constructive: trues-unbounded (as DATA) ⟹ constant-`true` subsequence.**  The
    unboundedness witness is supplied as a choice function `H : ∀ m, { n // m < n ∧ a n = true }`
    (Skolemized — extracting a *function* from `∀ m, ∃ n, …` is exactly the choice the residue
    refuses; supplying it as data is the constructive core).  The greedy index map
    `g (k+1) = findFrom a (g k + 1) (witness-bound)` then lands on a fresh `true` each step. -/
theorem subseq_of_unbounded_true (a : Nat → Bool)
    (H : ∀ m, { n : Nat // m < n ∧ a n = true }) : HasConstSubseq a := by
  -- `step c` : from a current index `c`, produce a true index `> c` (via the window search).
  have step : ∀ c : Nat, { n : Nat // c < n ∧ a n = true } := by
    intro c
    obtain ⟨n, hcn, han⟩ := H c
    -- search the window [c+1, c+1 + (n+1)) for the first true; n is in range (avoids `-`)
    have hbound : n < (c + 1) + (n + 1) :=
      Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
        (Nat.le_trans (Nat.le_trans (Nat.le_add_left (n + 1) c) (Nat.le_succ _))
          (Nat.le_of_eq (Nat.add_right_comm c (n + 1) 1)))
    have hge : c + 1 ≤ n := hcn
    have hsucc := findFrom_succeeds a (n + 1) (c + 1) n hge hbound han
    refine ⟨findFrom a (c + 1) (n + 1), ?_, hsucc.1⟩
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self c) (findFrom_ge a (n + 1) (c + 1))
  -- iterate `step` from a starting true index
  obtain ⟨n0, _, han0⟩ := H 0
  -- gpair k : the index after k steps, with proof it is true and strictly above previous
  let gpair : Nat → { p : Nat // a p = true } :=
    Nat.rec ⟨n0, han0⟩ (fun _ prev => ⟨(step prev.1).1, (step prev.1).2.2⟩)
  refine ⟨true, fun k => (gpair k).1, ?_, fun k => (gpair k).2⟩
  -- strict monotonicity: each step strictly increases; chain it
  have hstep : ∀ k, (gpair k).1 < (gpair (k + 1)).1 := by
    intro k
    show (gpair k).1 < (step (gpair k).1).1
    exact (step (gpair k).1).2.1
  intro i j hij
  -- gpair is strictly increasing because each successor is strictly above; induct on j
  induction j with
  | zero => exact absurd hij (Nat.not_lt_zero i)
  | succ j ih =>
    rcases Nat.lt_or_ge i j with h | h
    · exact Nat.lt_trans (ih h) (hstep j)
    · have : i = j := Nat.le_antisymm (Nat.le_of_lt_succ hij) h
      rw [this]; exact hstep j

/-- **Constructive: eventually-all-false ⟹ constant-`false` subsequence.**  Past the
    threshold `M`, every index is `false`; the shift `g k = M + k` is strictly increasing
    and lands on `false`. -/
theorem subseq_of_eventually_false (a : Nat → Bool)
    (H : ∃ M, ∀ n, M ≤ n → a n = false) : HasConstSubseq a := by
  rcases H with ⟨M, hM⟩
  refine ⟨false, fun k => M + k, ?_, ?_⟩
  · intro i j hij; exact Nat.add_lt_add_left hij M
  · intro k; exact hM (M + k) (Nat.le_add_right M k)

/-! ## Reverse calibration: binary BW ⟹ LPO  (rung = LPO, the strongest base principle)

Feed BW the **prefix-OR** stream `prefixOr f n = f 0 || … || f n` (monotone).  A constant
subsequence's value decides `f`:

* value `true`  → `prefixOr` is true at `g 0`, so some `f i = true` (`i ≤ g 0`) → `∃ true`;
* value `false` → `prefixOr` is false on the unbounded range of `g`; monotone ⟹ `prefixOr`
  is false everywhere ⟹ every `f n = false`.

So `(∀ a, HasConstSubseq a) ⟹ LPO`.  This pins binary BW at **≥ LPO**: it is at least as
non-constructive as the strongest base omniscience principle. -/

/-- Prefix-OR: `prefixOr f n = f 0 || f 1 || … || f n`. -/
def prefixOr (f : Nat → Bool) : Nat → Bool
  | 0     => f 0
  | n + 1 => prefixOr f n || f (n + 1)

/-- `f` fires below `n` ⟹ `prefixOr` is true at `n`. -/
theorem prefixOr_of_fire (f : Nat → Bool) :
    ∀ n i, i ≤ n → f i = true → prefixOr f n = true
  | 0,     i, hi, hfi => by
    have : i = 0 := Nat.le_zero.mp hi
    rw [this] at hfi; exact hfi
  | n + 1, i, hi, hfi => by
    show (prefixOr f n || f (n + 1)) = true
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · have hp : prefixOr f n = true := prefixOr_of_fire f n i (Nat.le_of_lt_succ h) hfi
      rw [hp]; rfl
    · have hin : i = n + 1 := Nat.le_antisymm hi h
      rw [hin] at hfi
      rw [hfi]
      cases hp : prefixOr f n with
      | true  => rfl
      | false => rfl

/-- `prefixOr f n = false ⟹ f n = false` (the last disjunct). -/
theorem fire_false_of_prefixOr_false (f : Nat → Bool) :
    ∀ n, prefixOr f n = false → f n = false
  | 0,     h => h
  | n + 1, h => by
    show f (n + 1) = false
    -- (prefixOr f n || f (n+1)) = false ⟹ f (n+1) = false
    have hh : (prefixOr f n || f (n + 1)) = false := h
    cases hfn : f (n + 1) with
    | false => rfl
    | true  =>
      exfalso
      cases hp : prefixOr f n with
      | true  => rw [hp, hfn] at hh; exact Bool.noConfusion hh
      | false => rw [hp, hfn] at hh; exact Bool.noConfusion hh

/-- ★★★ **Binary Bolzano–Weierstrass ⟹ LPO**, ∅-axiom.  The omniscience principle is the
    conclusion, not an assumption — so this is a genuine PURE calibration: BW is at least
    LPO-hard. -/
theorem lpo_of_bw (bw : ∀ a : Nat → Bool, HasConstSubseq a) : LPO := by
  intro f
  rcases bw (prefixOr f) with ⟨v, g, gmono, gconst⟩
  cases v with
  | true =>
    -- prefixOr f (g 0) = true ⟹ some f i = true for i ≤ g 0; recover the witness
    left
    have h0 : prefixOr f (g 0) = true := gconst 0
    -- extract a fire witness from prefixOr = true, by induction on the index
    exact prefixOr_true_imp_fire f (g 0) h0
  | false =>
    -- prefixOr f false on the unbounded range g ⟹ prefixOr false everywhere ⟹ f false
    right
    intro n
    -- g is strictly increasing, so g n ≥ n, hence n ≤ g n and prefixOr monotone-false
    have hgn : n ≤ g n := strictMono_ge g gmono n
    have hpref0 : prefixOr f (g n) = false := gconst n
    -- prefixOr is monotone: false at g n (≥ n) ⟹ false at n
    have : prefixOr f n = false := prefixOr_antitone_false f n (g n) hgn hpref0
    exact fire_false_of_prefixOr_false f n this
where
  /-- From `prefixOr f n = true` extract some `f i = true`. -/
  prefixOr_true_imp_fire (f : Nat → Bool) : ∀ n, prefixOr f n = true → ∃ i, f i = true
    | 0,     h => ⟨0, h⟩
    | n + 1, h => by
      have hh : (prefixOr f n || f (n + 1)) = true := h
      cases hfn : f (n + 1) with
      | true  => exact ⟨n + 1, hfn⟩
      | false =>
        cases hp : prefixOr f n with
        | true  => exact prefixOr_true_imp_fire f n hp
        | false => rw [hp, hfn] at hh; exact Bool.noConfusion hh
  /-- A strictly increasing `g` satisfies `n ≤ g n`. -/
  strictMono_ge (g : Nat → Nat) (gmono : ∀ i j, i < j → g i < g j) : ∀ n, n ≤ g n
    | 0     => Nat.zero_le _
    | n + 1 => Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (strictMono_ge g gmono n) (gmono n (n + 1) (Nat.lt_succ_self n)))
  /-- prefixOr is monotone, so `false` at a larger index forces `false` at a smaller one. -/
  prefixOr_antitone_false (f : Nat → Bool) : ∀ m n, m ≤ n → prefixOr f n = false → prefixOr f m = false
    | m, n, hmn, hn => by
      induction hmn with
      | refl => exact hn
      | @step n hmn ih =>
        apply ih
        show prefixOr f n = false
        have hh : (prefixOr f n || f (n + 1)) = false := hn
        cases hp : prefixOr f n with
        | false => rfl
        | true  => rw [hp] at hh; exact Bool.noConfusion hh

/-! ## Forward calibration — where LPO is *not* enough (the honest rung)

The reverse direction pins binary BW at **≥ LPO**.  The forward direction does **not** close
at plain LPO: extracting the constant subsequence requires deciding the **Π⁰₂** statement
"`true` occurs unboundedly often" (its negation is "eventually all `false`", a **Σ⁰₂**
statement).  Plain LPO decides only Π⁰₁ (`Pi01Decision.lpo_decides_pi01`); Σ⁰₂/Π⁰₂ deciding
is strictly stronger.  Two honest fragments LPO *does* deliver:

1. **`subseq_of_unbounded_true`** — once unboundedness is available **as data** (the
   Skolem/choice function), the extraction is fully constructive (∅-axiom, no omniscience).
   The omniscience/choice content is exactly the Prop-∃ → data step that LPO cannot perform
   for free (extracting a *witness function* from `∀ m, ∃ n, …` is the residue's refused move).
2. **`lpo_decides_const_false_or_some_true`** (below) — LPO settles the *trivial* value
   dichotomy "(constant-`false` subsequence) ∨ (some `true`)".  This is Σ⁰₁ (`∃ true`), so
   LPO suffices; but it stops short of the *cofinal-value* decision (which `true`-vs-`false`
   occurs **infinitely often**) — that is the Σ⁰₂ content above LPO. -/

/-- ★ **LPO settles the trivial value dichotomy.**  Either `a` is everywhere `false` (giving
    the constant-`false` subsequence `g = id`) or some index is `true`.  Σ⁰₁-level, so LPO
    suffices — but this is *not* the full BW conclusion (the cofinal-value question is Σ⁰₂). -/
theorem lpo_decides_const_false_or_some_true (hlpo : LPO) (a : Nat → Bool) :
    HasConstSubseq a ∨ (∃ n, a n = true) :=
  (hlpo a).elim
    (fun he => Or.inr he)
    (fun hall => Or.inl (subseq_of_eventually_false a ⟨0, fun n _ => hall n⟩))

end E213.Lib.Math.Logic.BolzanoWeierstrass
