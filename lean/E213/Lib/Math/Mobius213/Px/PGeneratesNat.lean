import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Math.Mobius213.Px.POrbitClosure
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Lib.Math.NatRing

/-!
# Mobius213.Px.PGeneratesNat — P generates ALL natural numbers

The Möbius matrix `P = [[2,1],[1,1]]` carries enough structure
to generate every natural number ≥ 1 via its invariants:

  · `det(P) = 1`
  · `P[1][1] = NT = 2 = L(0)`
  · `tr(P) = NS = 3 = L(1)`

Since `gcd(2, 3) = 1`, the Chicken-McNugget / Sylvester-Frobenius
theorem tells us the largest integer NOT representable as
`2a + 3b` (a, b ≥ 0) is `2·3 − 2 − 3 = 1`.  Equivalently:

  **∀ n ≥ 2, ∃ a b : ℕ, n = 2a + 3b**

Combined with `1 = det(P)` (a direct P-invariant), we get:

  **∀ n ≥ 1, n is P-generated.**

This is STRONGER than the previous `NaturalnessClosure` which
only considered the *multiplicative* span `{1, 2, 3, 5}^×`
(which misses 7, 11, 13, ...).  The additive-multiplicative ring
closure of P-invariants is ALL of ℕ — trivially, because
`gcd(NT, NS) = gcd(2, 3) = 1`.

## Key insight (user observation)

> "모든 자연수들을 P 자체로 생성하는 이론을 만들어보자
>  (7 같은 수도 다 만들 수 있음)"

  · 7 = 2 + 2 + 3 (also = L(2) = trace(P²)).  Three P-entries.
  · 11 = 2·1 + 3·3 = 2+3+3+3.  Four P-entries (optimal).
  · 13 = 2·2 + 3·3 = 2+2+3+3+3.  Five P-entries.
  · ANY n ≥ 2: by strong induction with step −2.

The P-orbit ring is all of ℤ.  The P-additive span is all of ℕ≥2.
Combined with det=1, the P-span is all of ℕ≥1.

## Structure

  · §1 — `PGen` inductive predicate (additive generation from P-entries)
  · §2 — Chicken McNugget: ∀ n ≥ 2, ∃ a b, n = 2a + 3b
  · §3 — `PGen` contains all ℕ ≥ 1 (direct strong induction)
  · §4 — Concrete witnesses for "hard" numbers
  · §5 — Depth theory (minDepth, optimality, greedy formula)
  · §6 — Comparison with previous naturalness claims
  · §7 — The deeper reading: WHY P generates ℕ (Fibonacci necessity)
  · §8 — Semiring closure (PGen n ↔ n ≥ 1, exact characterization)
  · §9 — Explicit prime generation catalog (primes ≤ 47)

All declarations PURE (∅-axiom) except `coprime_NS_NT`, whose
statement is `Nat.gcd NS NT = 1`: Lean-core `Nat.gcd` is defined by
well-founded recursion whose kernel reduction / equation lemmas
irreducibly carry `[propext]` in this toolchain (even `rfl` /
`decide` / `unfold` on a closed `Nat.gcd` literal is propext-dirty).
The PURE coprimality fact lives as `gcd213_succ_self` in
`E213.Meta.Nat.Gcd213` (using the ∅-axiom `gcd213`); `coprime_NS_NT`
is retained verbatim only as the core-`Nat.gcd` mirror.  No
kernel-external compiled-evaluation tactic.
-/

namespace E213.Lib.Math.Mobius213.Px.PGeneratesNat

open E213.Lib.Physics.Simplex.Counts (NS NT d)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Meta.Nat.AddMod213 (div_add_mod add_mod_gen mod_mod)
open E213.Tactic.NatHelper (mul_mod_right sub_add_cancel)
open E213.Lib.Math.NatRing (nat_add_mul)

/-! ## §1 — P-generation predicate

`PGen n` means n is reachable from P-invariants `{det=1, NT=2, NS=3}`
via addition and multiplication. -/

/-- The P-generation predicate on ℕ: the smallest set containing
    det(P)=1, NT=2, NS=3 and closed under + and ·. -/
inductive PGen : Nat → Prop
  | det_one  : PGen 1
  | entry_NT : PGen NT
  | trace_NS : PGen NS
  | add      : ∀ {a b}, PGen a → PGen b → PGen (a + b)
  | mul      : ∀ {a b}, PGen a → PGen b → PGen (a * b)

/-- 2 ∈ PGen (= NT = P entry). -/
theorem pgen_two : PGen 2 := PGen.entry_NT

/-- 3 ∈ PGen (= NS = trace P). -/
theorem pgen_three : PGen 3 := PGen.trace_NS

/-- 4 = 2 + 2 ∈ PGen. -/
theorem pgen_four : PGen 4 :=
  (show (2 + 2 : Nat) = 4 from rfl) ▸ PGen.add PGen.entry_NT PGen.entry_NT

/-- 5 = 2 + 3 ∈ PGen (= d = disc P). -/
theorem pgen_five : PGen 5 :=
  (show (NT + NS : Nat) = 5 from rfl) ▸ PGen.add PGen.entry_NT PGen.trace_NS

/-- 6 = 3 + 3 ∈ PGen (= NS·NT). -/
theorem pgen_six : PGen 6 :=
  (show (NS + NS : Nat) = 6 from rfl) ▸ PGen.add PGen.trace_NS PGen.trace_NS

/-- ★ 7 = 2 + 2 + 3 ∈ PGen (also = L(2) = trace(P²)). -/
theorem pgen_seven : PGen 7 :=
  (show (NT + NT + NS : Nat) = 7 from rfl) ▸
    PGen.add (PGen.add PGen.entry_NT PGen.entry_NT) PGen.trace_NS

/-! ## §2 — Chicken McNugget for (2, 3)

**Theorem**: ∀ n ≥ 2, ∃ a b : ℕ, n = 2·a + 3·b.

Proof by strong induction:
  · n = 2: a=1, b=0
  · n = 3: a=0, b=1
  · n ≥ 4: n−2 ≥ 2, by IH ∃ a b, n−2 = 2a+3b, so n = 2(a+1)+3b. -/

/-- Representability as `2a + 3b`. -/
def Rep23 (n : Nat) : Prop := ∃ a b : Nat, n = 2 * a + 3 * b

theorem rep23_two : Rep23 2 := ⟨1, 0, rfl⟩
theorem rep23_three : Rep23 3 := ⟨0, 1, rfl⟩

/-- If `Rep23 n` then `Rep23 (n + 2)`:  n = 2a+3b → n+2 = 2(a+1)+3b. -/
theorem rep23_step (n : Nat) (h : Rep23 n) : Rep23 (n + 2) :=
  let ⟨a, b, ha⟩ := h
  ⟨a + 1, b, by
    -- n + 2 = 2*(a+1) + 3*b.  2*(a+1) = 2*a + 2 (= Nat.mul_succ).
    rw [ha, Nat.mul_succ]
    -- (2*a + 3*b) + 2 = (2*a + 2) + 3*b
    rw [Nat.add_right_comm (2 * a) (3 * b) 2]⟩

/-- ★★ **Chicken McNugget for (2,3)**: every n ≥ 2 is `2a + 3b`.
    Proof: match on n = 2, 3, or n+4 (use IH on n+2). -/
theorem chicken_mcnugget_23 : ∀ n : Nat, 2 ≤ n → Rep23 n := by
  intro n
  match n with
  | 0 => intro h; exact absurd h (by decide)
  | 1 => intro h; exact absurd h (by decide)
  | 2 => intro _; exact rep23_two
  | 3 => intro _; exact rep23_three
  | n + 4 => intro _
             have ih := chicken_mcnugget_23 (n + 2) (Nat.le_add_left 2 n)
             exact rep23_step (n + 2) ih

/-! ## §3 — PGen contains all ℕ ≥ 1

Direct strong induction on n: base cases 2, 3; step n→n+2.
The key insight: adding NT=2 to any PGen number gives PGen (n+2). -/

/-- ★★★ **P generates every n ≥ 2**: additive closure of {NT, NS}
    covers all of ℕ≥2.  Proof by strong induction with step −2. -/
theorem pgen_ge_two : ∀ n : Nat, 2 ≤ n → PGen n := by
  intro n hn
  match n, hn with
  | 2, _ => exact PGen.entry_NT
  | 3, _ => exact PGen.trace_NS
  | n + 4, _ =>
    have ih : PGen (n + 2) := pgen_ge_two (n + 2) (Nat.le_add_left 2 n)
    have step : PGen ((n + 2) + 2) := PGen.add ih PGen.entry_NT
    -- (n+2)+2 = n+4 by defeq on the index
    exact step

/-- ★★★★ **P generates every n ≥ 1**: all of ℕ \ {0} is P-generated.
    Combines `PGen.det_one` (for n=1) with `pgen_ge_two` (for n≥2). -/
theorem pgen_all_pos : ∀ n : Nat, 1 ≤ n → PGen n := by
  intro n hn
  match n, hn with
  | 1, _ => exact PGen.det_one
  | n + 2, _ => exact pgen_ge_two (n + 2) (Nat.le_add_left 2 n)

/-! ## §4 — Concrete witnesses for notable "hard" numbers

These are numbers previously considered "non-atomic-derivable"
in the multiplicative sense, but trivially P-generated additively. -/

/-- 7 = 2·2 + 3·1 (also = L(2) = trace(P²)). -/
theorem seven_witness : (7 : Nat) = 2 * 2 + 3 * 1 := by decide

/-- 11 = 2·1 + 3·3 (optimal depth = 4). -/
theorem eleven_witness : (11 : Nat) = 2 * 1 + 3 * 3 := by decide

/-- 13 = 2·2 + 3·3. -/
theorem thirteen_witness : (13 : Nat) = 2 * 2 + 3 * 3 := by decide

/-- 14 = 2·4 + 3·2 (the mod-13 period). -/
theorem fourteen_witness : (14 : Nat) = 2 * 4 + 3 * 2 := by decide

/-- 29 = 2·1 + 3·9. -/
theorem twentynine_witness : (29 : Nat) = 2 * 1 + 3 * 9 := by decide

/-- 97 = 2·47 + 3·1 (the largest catalogued prime). -/
theorem ninetyseven_witness : (97 : Nat) = 2 * 47 + 3 * 1 := by decide

/-- Every number 2..20 has a Rep23 witness. Exhaustive catalog. -/
theorem rep23_catalog_small :
    Rep23 2 ∧ Rep23 3 ∧ Rep23 4 ∧ Rep23 5 ∧ Rep23 6
    ∧ Rep23 7 ∧ Rep23 8 ∧ Rep23 9 ∧ Rep23 10
    ∧ Rep23 11 ∧ Rep23 12 ∧ Rep23 13 ∧ Rep23 14
    ∧ Rep23 15 ∧ Rep23 16 ∧ Rep23 17 ∧ Rep23 18
    ∧ Rep23 19 ∧ Rep23 20 :=
  ⟨⟨1,0,rfl⟩, ⟨0,1,rfl⟩, ⟨2,0,rfl⟩, ⟨1,1,rfl⟩, ⟨3,0,rfl⟩,
   ⟨2,1,rfl⟩, ⟨4,0,rfl⟩, ⟨3,1,rfl⟩, ⟨5,0,rfl⟩,
   ⟨4,1,rfl⟩, ⟨6,0,rfl⟩, ⟨2,3,rfl⟩, ⟨4,2,rfl⟩,
   ⟨6,1,rfl⟩, ⟨8,0,rfl⟩, ⟨7,1,rfl⟩, ⟨9,0,rfl⟩,
   ⟨8,1,rfl⟩, ⟨10,0,rfl⟩⟩

/-! ## §5 — Depth theory

The **additive P-depth** of n is the minimum number of P-entry
summands needed: `depth(n) = min {a + b : 2a + 3b = n}`.

  · depth(2) = 1 (one NT)
  · depth(3) = 1 (one NS)
  · depth(7) = 3 (two NT + one NS)
  · depth(1) = 1 (one det — special)

Optimal strategy: use as many NS=3 as possible (greedy mod 3).
Formula for n ≥ 2:
  · n ≡ 0 mod 3 → n/3
  · n ≡ 1 mod 3 → (n−4)/3 + 2  (subtract two 2's, rest in 3's)
  · n ≡ 2 mod 3 → (n−2)/3 + 1  (subtract one 2, rest in 3's)

All depth theorems proved via `decide` (∅-axiom). -/

/-- Minimum additive depth for n ≥ 2 (minimum summand count).
    For n=0: 0 (vacuous). For n=1: 1 (det). For n≥2: greedy-3 formula. -/
def minDepth : Nat → Nat
  | 0 => 0
  | 1 => 1  -- special: det(P) directly
  | n + 2 =>
    let m := n + 2
    let r := m % 3
    if r == 0 then m / 3
    else if r == 2 then 1 + (m - 2) / 3
    else 2 + (m - 4) / 3

theorem minDepth_2 : minDepth 2 = 1 := by decide
theorem minDepth_3 : minDepth 3 = 1 := by decide
theorem minDepth_7 : minDepth 7 = 3 := by decide
theorem minDepth_11 : minDepth 11 = 4 := by decide
theorem minDepth_13 : minDepth 13 = 5 := by decide
theorem minDepth_97 : minDepth 97 = 33 := by decide
theorem minDepth_100 : minDepth 100 = 34 := by decide

/-- Depth is always bounded: minDepth n ≤ n for all n.
    Proof: n/3 ≤ n (or n/3 + 1, 2 ≤ n). -/
theorem minDepth_le (n : Nat) : minDepth n ≤ n := by
  match n with
  | 0 => decide
  | 1 => decide
  | k + 2 =>
    show minDepth (k + 2) ≤ k + 2
    unfold minDepth
    -- m = k + 2; result is one of m/3, 1 + (m-2)/3, 2 + (m-4)/3.
    -- Reveal the desugared `if … = true` form and case-split PURELY
    -- (avoiding `simp [beq_iff_eq]` / `split`, both of which leak propext).
    show (if ((k + 2) % 3 == 0) = true then (k + 2) / 3
          else if ((k + 2) % 3 == 2) = true then 1 + ((k + 2) - 2) / 3
          else 2 + ((k + 2) - 4) / 3) ≤ k + 2
    -- Three branch bounds, each via the PURE `div_le_self_pos`.
    have H0 : (k + 2) / 3 ≤ k + 2 :=
      E213.Meta.Nat.NatDiv213.div_le_self_pos (k + 2) 3 (by decide)
    have H1 : 1 + ((k + 2) - 2) / 3 ≤ k + 2 := by
      -- (k+2)-2 = k (defeq); k/3 ≤ k; 1 + k/3 ≤ 1 + k = k + 1 ≤ k + 2.
      have hk : ((k + 2) - 2) / 3 ≤ k :=
        E213.Meta.Nat.NatDiv213.div_le_self_pos ((k + 2) - 2) 3 (by decide)
      have h2 : 1 + ((k + 2) - 2) / 3 ≤ 1 + k := Nat.add_le_add_left hk 1
      have h3 : (1 : Nat) + k ≤ k + 2 := by
        rw [Nat.add_comm 1 k]; exact Nat.le_succ (k + 1)
      exact Nat.le_trans h2 h3
    have H2 : 2 + ((k + 2) - 4) / 3 ≤ k + 2 := by
      -- ((k+2)-4)/3 ≤ (k+2)-4 ≤ k; 2 + … ≤ 2 + ((k+2)-4) ≤ 2 + k = k + 2.
      have hk : ((k + 2) - 4) / 3 ≤ (k + 2) - 4 :=
        E213.Meta.Nat.NatDiv213.div_le_self_pos ((k + 2) - 4) 3 (by decide)
      have hsub : (k + 2) - 4 ≤ k := by
        -- (k+2)-4 = k-2 (defeq) ≤ k.
        show (k - 2) ≤ k
        exact Nat.sub_le k 2
      have h2 : 2 + ((k + 2) - 4) / 3 ≤ 2 + k :=
        Nat.add_le_add_left (Nat.le_trans hk hsub) 2
      have h3 : (2 : Nat) + k ≤ k + 2 := Nat.le_of_eq (Nat.add_comm 2 k)
      exact Nat.le_trans h2 h3
    cases h0 : (k + 2) % 3 == 0 with
    | true => rw [if_pos rfl]; exact H0
    | false =>
      rw [if_neg Bool.false_ne_true]
      cases h2 : (k + 2) % 3 == 2 with
      | true => rw [if_pos rfl]; exact H1
      | false => rw [if_neg Bool.false_ne_true]; exact H2

/-- The greedy formula witnesses: for small n, n = 2·a + 3·b where a+b = minDepth n.
    This validates the minDepth function computes correct optima. -/
theorem minDepth_witness_catalog :
    -- n=2: 2 = 2·1 + 3·0, depth 1
    (∃ a b : Nat, 2 = 2 * a + 3 * b ∧ a + b = minDepth 2)
    -- n=3: 3 = 2·0 + 3·1, depth 1
    ∧ (∃ a b : Nat, 3 = 2 * a + 3 * b ∧ a + b = minDepth 3)
    -- n=7: 7 = 2·2 + 3·1, depth 3
    ∧ (∃ a b : Nat, 7 = 2 * a + 3 * b ∧ a + b = minDepth 7)
    -- n=13: 13 = 2·2 + 3·3, depth 5
    ∧ (∃ a b : Nat, 13 = 2 * a + 3 * b ∧ a + b = minDepth 13)
    -- n=97: 97 = 2·2 + 3·31, depth 33
    ∧ (∃ a b : Nat, 97 = 2 * a + 3 * b ∧ a + b = minDepth 97) :=
  ⟨⟨1, 0, by decide, by decide⟩,
   ⟨0, 1, by decide, by decide⟩,
   ⟨2, 1, by decide, by decide⟩,
   ⟨2, 3, by decide, by decide⟩,
   ⟨2, 31, by decide, by decide⟩⟩

/-- PURE algebraic identity `3*(a+b) = (2a+3b) + a`.  Used by
    `minDepth_optimal`.  Proved with the PURE `nat_add_mul`. -/
private theorem key3 (a b : Nat) : 3 * (a + b) = (2 * a + 3 * b) + a := by
  rw [Nat.mul_add]
  rw [show (3 : Nat) * a = 2 * a + a from by
    rw [show (3 : Nat) = 2 + 1 from rfl, nat_add_mul, Nat.one_mul]]
  rw [Nat.add_assoc (2 * a) a (3 * b), Nat.add_comm a (3 * b),
      ← Nat.add_assoc (2 * a) (3 * b) a]

/-- The minDepth formula gives the optimum: for any n ≥ 2 and
    any representation n = 2a + 3b, we have a + b ≥ minDepth n.
    (This is the key optimality claim; proof by mod-3 case analysis.)

    ∅-axiom proof.  The crux: `3*(a+b) = (k+2)+a` (`key3`), so
    `greedy(m) ≤ a+b ⟺ 3*greedy(m) ≤ (k+2)+a` (no division on the
    comparison), and `3*(m/3) ≤ m` (`div_add_mod`) handles each
    mod-3 branch.  The residue of `a` (`a ≥ 1` for `m%3=2`, `a ≥ 2`
    for `m%3=1`) is forced by `m = 2a+3b` via `mul_mod_right`. -/
theorem minDepth_optimal (n a b : Nat) (hn : 2 ≤ n) (hrep : n = 2 * a + 3 * b) :
    minDepth n ≤ a + b := by
  -- Put n in the `k + 2` form so `minDepth` reduces to its if-expression.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, (sub_add_cancel hn).symm⟩
  show minDepth (k + 2) ≤ a + b
  unfold minDepth
  -- Reveal the desugared `if … = true` form (PURE branch split below).
  show (if ((k + 2) % 3 == 0) = true then (k + 2) / 3
        else if ((k + 2) % 3 == 2) = true then 1 + ((k + 2) - 2) / 3
        else 2 + ((k + 2) - 4) / 3) ≤ a + b
  -- 3*(a+b) = (k+2)+a.
  have hkey : 3 * (a + b) = (k + 2) + a := by rw [hrep]; exact key3 a b
  -- Reduce `g ≤ a+b` to `3*g ≤ (k+2)+a` (multiply through, no division).
  have reduce : ∀ g : Nat, 3 * g ≤ (k + 2) + a → g ≤ a + b := fun g hg =>
    Nat.le_of_mul_le_mul_left (hkey ▸ hg) (by decide)
  -- `3*(x/3) ≤ x` for every x (PURE via div_add_mod).
  have cxc : ∀ x : Nat, 3 * (x / 3) ≤ x := fun x =>
    Nat.le_trans (Nat.le_add_right (3 * (x / 3)) (x % 3))
      (Nat.le_of_eq (div_add_mod x 3))
  cases h0 : (k + 2) % 3 == 0 with
  | true =>
    rw [if_pos rfl]
    exact reduce _ (Nat.le_trans (cxc (k + 2)) (Nat.le_add_right (k + 2) a))
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases h2 : (k + 2) % 3 == 2 with
    | true =>
      rw [if_pos rfl]
      -- m % 3 = 2 ⇒ a ≥ 1 (else m = 3b ⇒ m%3 = 0).
      have ha1 : 1 ≤ a := by
        cases a with
        | zero =>
          exfalso
          have hk2 : k + 2 = 3 * b := by rw [hrep, Nat.mul_zero, Nat.zero_add]
          rw [hk2, mul_mod_right 3 b] at h2
          exact Bool.noConfusion h2
        | succ a0 => exact Nat.succ_le_succ (Nat.zero_le a0)
      apply reduce
      rw [show 3 * (1 + ((k + 2) - 2) / 3) = 3 + 3 * (((k + 2) - 2) / 3) from by
        rw [Nat.mul_add, Nat.mul_one]]
      have step1 : 3 + 3 * (((k + 2) - 2) / 3) ≤ 3 + ((k + 2) - 2) :=
        Nat.add_le_add_left (cxc ((k + 2) - 2)) 3
      have step2 : 3 + ((k + 2) - 2) = (k + 2) + 1 := by
        show 3 + k = (k + 2) + 1; rw [Nat.add_comm 3 k]
      have step3 : (k + 2) + 1 ≤ (k + 2) + a := Nat.add_le_add_left ha1 (k + 2)
      exact Nat.le_trans step1 (Nat.le_trans (Nat.le_of_eq step2) step3)
    | false =>
      rw [if_neg Bool.false_ne_true]
      -- m % 3 = 1 ⇒ a ≥ 2 (a=0 ⇒ m%3=0; a=1 ⇒ m%3=2).
      have ha2 : 2 ≤ a := by
        cases a with
        | zero =>
          exfalso
          have hk2 : k + 2 = 3 * b := by rw [hrep, Nat.mul_zero, Nat.zero_add]
          rw [hk2, mul_mod_right 3 b] at h0
          exact Bool.noConfusion h0
        | succ a0 =>
          cases a0 with
          | zero =>
            exfalso
            have hk2 : k + 2 = 2 + 3 * b := by rw [hrep]
            rw [hk2, add_mod_gen 2 (3 * b) 3, mul_mod_right 3 b, Nat.add_zero, mod_mod]
              at h2
            exact Bool.noConfusion h2
          | succ a1 => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le a1))
      -- a ≥ 2 ⇒ k+2 = 2a+3b ≥ 4.
      have hk4 : 4 ≤ k + 2 := by
        rw [hrep]
        exact Nat.le_trans (Nat.mul_le_mul_left 2 ha2) (Nat.le_add_right (2 * a) (3 * b))
      apply reduce
      rw [show 3 * (2 + ((k + 2) - 4) / 3) = 6 + 3 * (((k + 2) - 4) / 3) from by
        rw [Nat.mul_add]]
      have step1 : 6 + 3 * (((k + 2) - 4) / 3) ≤ 6 + ((k + 2) - 4) :=
        Nat.add_le_add_left (cxc ((k + 2) - 4)) 6
      have hsac : ((k + 2) - 4) + 4 = k + 2 := sub_add_cancel hk4
      have step2 : 6 + ((k + 2) - 4) = (k + 2) + 2 := by
        rw [Nat.add_comm 6 ((k + 2) - 4)]
        show ((k + 2) - 4) + 6 = (k + 2) + 2
        rw [show (6 : Nat) = 4 + 2 from rfl, ← Nat.add_assoc ((k + 2) - 4) 4 2, hsac]
      have step3 : (k + 2) + 2 ≤ (k + 2) + a := Nat.add_le_add_left ha2 (k + 2)
      exact Nat.le_trans step1 (Nat.le_trans (Nat.le_of_eq step2) step3)

/-! ## §6 — Comparison with previous naturalness claims

The multiplicative span of `{1, 2, 3, 5}` (= NaturalnessClosure)
misses all primes > 5.  But the ADDITIVE closure of just `{2, 3}`
already covers all of ℕ≥2.  This resolves the "7 ∉ atomic closure"
issue entirely:

  · **Multiplicative only**: {1,2,3,5}^× = {1,2,3,4,5,6,8,9,10,...}
    — misses 7, 11, 13, 14, ...
  · **Additive**: {2,3}^+ = {2,3,4,5,6,7,8,...} = ℕ≥2
    — covers everything ≥ 2
  · **P-generated**: {det=1} ∪ {2,3}^+ = ℕ≥1 = ℕ \ {0}
    — ALL positive naturals

The "non-atomic" primes (7, 11, 13, ...) were never a genuine
boundary violation.  P contains 2 and 3 as entries; their
additive closure is universal.  The restrictive "multiplicative-only"
reading was an artificial limitation that the matrix itself does
not impose. -/

/-- ★★★★★★★★★★ **P-generates-ℕ master theorem**: bundles the
    complete P-generation result.

    (a) det(P) = 1 provides the unit
    (b) NT = 2, NS = 3 are coprime (gcd = 1)
    (c) Chicken McNugget: ∀ n ≥ 2, n = 2a + 3b
    (d) Therefore: ∀ n ≥ 1, PGen n

    The Möbius matrix P = [[2,1],[1,1]] generates ALL positive
    natural numbers via its entries alone. -/
theorem p_generates_nat_master :
    -- (a) Unit
    (PGen 1)
    -- (b) Coprime generators
    ∧ (PGen 2 ∧ PGen 3)
    -- (c) Chicken McNugget for (2,3)
    ∧ (∀ n : Nat, 2 ≤ n → Rep23 n)
    -- (d) Universal generation
    ∧ (∀ n : Nat, 1 ≤ n → PGen n)
    -- (e) Notable former "non-atomic" numbers are PGen
    ∧ (PGen 7 ∧ PGen 11 ∧ PGen 13 ∧ PGen 14 ∧ PGen 29) :=
  ⟨PGen.det_one,
   ⟨PGen.entry_NT, PGen.trace_NS⟩,
   chicken_mcnugget_23,
   pgen_all_pos,
   ⟨pgen_all_pos 7 (by decide),
    pgen_all_pos 11 (by decide),
    pgen_all_pos 13 (by decide),
    pgen_all_pos 14 (by decide),
    pgen_all_pos 29 (by decide)⟩⟩

/-! ## §7 — The deeper reading: WHY P generates ℕ

It's not accidental that P generates all naturals. The reason is:

  · P has **consecutive Fibonacci entries** (1, 1, 1, 2) at P¹
  · Consecutive Fibonacci numbers are always coprime: gcd(Fₙ, Fₙ₊₁) = 1
  · In particular: gcd(F₃, F₄) = gcd(2, 3) = 1
  · The Frobenius number of two coprime integers a, b is ab − a − b
  · For (2,3): Frobenius = 2·3 − 2 − 3 = 1

So the Fibonacci structure of P FORCES universal generation.
Any matrix whose entries include consecutive Fibonacci numbers
generates all naturals.  For P = [[F₄, F₃], [F₃, F₂]] = [[2,1],[1,1]]:
  · Entries {F₂, F₃, F₄} = {1, 1, 2}
  · trace = F₄ + F₂ = 2 + 1 = 3 = F₄ + F₂ (= NS)
  · gcd(F₃, F₃+F₂) = gcd(1, 2) — not helpful
  · But gcd(trace, entry) = gcd(3, 2) = 1 ← THIS forces surjectivity

The surjectivity of P onto ℕ is a CONSEQUENCE of:
  · Fibonacci structure (P = Q²)
  · Coprimality of consecutive Fibonacci numbers
  · Chicken McNugget theorem

This closes the "naturalness boundary" discussion completely. -/

/-- Fibonacci coprimality forces P-universality:
    gcd(NS, NT) = gcd(trace P, P₁₁) = gcd(3, 2) = 1.

    NOTE (axiom residue): this is the only non-PURE declaration in the
    file — `[propext]`, irreducible because its statement uses Lean-core
    `Nat.gcd`, whose well-founded-recursion reduction carries `propext`
    even under `rfl`.  The ∅-axiom form is `gcd213_succ_self` in
    `E213.Meta.Nat.Gcd213`. -/
theorem coprime_NS_NT : Nat.gcd NS NT = 1 := by decide

/-- The Frobenius number of (NT, NS) = (2, 3) is 1:
    the largest non-representable integer is 1.
    Every n ≥ 2 is representable. -/
theorem frobenius_NT_NS : NT * NS - NT - NS = 1 := by decide

/-! ## §8 — Semiring closure properties

PGen is closed under addition and multiplication (by construction),
contains 1 (unit), and is closed under 0-absorption.  Therefore
PGen characterizes exactly ℕ≥1 = ℕ \ {0}.  We prove the
exact characterization: `PGen n ↔ 1 ≤ n`. -/

/-- 0 is NOT P-generated.  The only non-PGen natural is 0. -/
theorem not_pgen_zero : ¬ PGen 0 := by
  intro h
  have hmain : ∀ m, PGen m → m ≥ 1 := by
    intro m hm
    induction hm with
    | det_one => decide
    | entry_NT => show NT ≥ 1; unfold NT; decide
    | trace_NS => show NS ≥ 1; unfold NS; decide
    | @add a b _ _ ih_a ih_b =>
      -- a ≥ 1 ⇒ a + b ≥ 1 (monotone in the added b).
      exact Nat.le_trans ih_a (Nat.le_add_right a b)
    | @mul a b _ _ ih_a ih_b =>
      -- a ≥ 1 and b ≥ 1, so a * b ≥ 1 * 1 = 1
      have ha : a ≥ 1 := ih_a
      have hb : b ≥ 1 := ih_b
      exact Nat.le_trans (by decide : 1 ≤ 1 * 1) (Nat.mul_le_mul ha hb)
  exact absurd (hmain 0 h) (Nat.not_succ_le_zero 0)

/-- PGen values are always positive. -/
theorem pgen_pos {n : Nat} (h : PGen n) : 1 ≤ n := by
  induction h with
  | det_one => decide
  | entry_NT => show 1 ≤ NT; unfold NT; decide
  | trace_NS => show 1 ≤ NS; unfold NS; decide
  | @add a b _ _ ih_a ih_b =>
    exact Nat.le_trans ih_a (Nat.le_add_right a b)
  | @mul a b _ _ ih_a ih_b =>
    have ha : a ≥ 1 := ih_a
    have hb : b ≥ 1 := ih_b
    exact Nat.le_trans (by decide : 1 ≤ 1 * 1) (Nat.mul_le_mul ha hb)

/-- ★★★★★ **Exact characterization**: PGen n ↔ n ≥ 1.
    P-generation is EXACTLY the positive naturals. -/
theorem pgen_iff_pos (n : Nat) : PGen n ↔ 1 ≤ n :=
  ⟨pgen_pos, pgen_all_pos n⟩

/-- PGen is closed under successor: if PGen n then PGen (n+1).
    (Since n ≥ 1, n+1 ≥ 2, automatic from pgen_ge_two.) -/
theorem pgen_succ {n : Nat} (_ : PGen n) : PGen (n + 1) :=
  pgen_all_pos (n + 1) (Nat.le_add_left 1 n)

/-- PGen forms a sub-semiring: closed under +, ·, contains 1.
    Bundled as a triple of closure properties. -/
theorem pgen_semiring_closure :
    -- (i) Contains multiplicative identity
    (PGen 1)
    -- (ii) Closed under addition
    ∧ (∀ a b, PGen a → PGen b → PGen (a + b))
    -- (iii) Closed under multiplication
    ∧ (∀ a b, PGen a → PGen b → PGen (a * b)) :=
  ⟨PGen.det_one,
   fun _ _ ha hb => PGen.add ha hb,
   fun _ _ ha hb => PGen.mul ha hb⟩

/-! ## §9 — Explicit generation chains for primes up to 50

For archival completeness and machine-verification of the theory,
we record explicit PGen construction chains for all primes ≤ 50. -/

theorem pgen_11 : PGen 11 := pgen_all_pos 11 (by decide)
theorem pgen_13 : PGen 13 := pgen_all_pos 13 (by decide)
theorem pgen_17 : PGen 17 := pgen_all_pos 17 (by decide)
theorem pgen_19 : PGen 19 := pgen_all_pos 19 (by decide)
theorem pgen_23 : PGen 23 := pgen_all_pos 23 (by decide)
theorem pgen_29 : PGen 29 := pgen_all_pos 29 (by decide)
theorem pgen_31 : PGen 31 := pgen_all_pos 31 (by decide)
theorem pgen_37 : PGen 37 := pgen_all_pos 37 (by decide)
theorem pgen_41 : PGen 41 := pgen_all_pos 41 (by decide)
theorem pgen_43 : PGen 43 := pgen_all_pos 43 (by decide)
theorem pgen_47 : PGen 47 := pgen_all_pos 47 (by decide)

/-- ★ The Rep23 representation provides explicit witnesses for all primes ≤ 47. -/
theorem prime_rep23_witnesses :
    Rep23 7 ∧ Rep23 11 ∧ Rep23 13 ∧ Rep23 17 ∧ Rep23 19
    ∧ Rep23 23 ∧ Rep23 29 ∧ Rep23 31 ∧ Rep23 37
    ∧ Rep23 41 ∧ Rep23 43 ∧ Rep23 47 :=
  ⟨⟨2,1,rfl⟩, ⟨4,1,rfl⟩, ⟨2,3,rfl⟩, ⟨4,3,rfl⟩, ⟨5,3,rfl⟩,
   ⟨10,1,rfl⟩, ⟨1,9,rfl⟩, ⟨2,9,rfl⟩, ⟨2,11,rfl⟩,
   ⟨1,13,rfl⟩, ⟨2,13,rfl⟩, ⟨1,15,rfl⟩⟩

end E213.Lib.Math.Mobius213.Px.PGeneratesNat
