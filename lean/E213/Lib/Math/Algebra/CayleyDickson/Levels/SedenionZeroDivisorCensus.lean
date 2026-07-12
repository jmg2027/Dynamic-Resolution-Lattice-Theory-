import E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionZeroDivisor

/-!
# Sedenion zero-divisor census — the L4 self-cover failure, counted

`SedenionZeroDivisor.lean` exhibits ONE zero-divisor pair.  This file
counts them (conjecture S6, `divergence_conjecture_slate.md`): over the
standard unit basis `e₀..e₁₅` (nested-CD encoding, welded below to the
existing witnesses), the census of ordered solutions

    (e_a + e_b) · (e_c ± e_d) = 0,   a < b,  c < d,  a,c ≥ 1

has the fully rigid structure (interpreter-verified over the whole
`15⁴·2` sweep; kernel-certified per chunk below):

  * left pairs with partners: exactly `(a, b)` with `a ∈ 1..7` (an
    OCTONION imaginary), `b ∈ 9..15`, `b ≠ a + 8` — **42 pairs**
    (`7 × 6`, the classical 42);
  * each such pair has exactly **4** partners;
  * per-`a` row sums: `[24 ×7, 0 ×8]`; **total = 42·4 = 168**.

The number `168 = |PSL(2,7)|` — the automorphism count of the Fano
plane, which IS the octonion multiplication table.  (That reading is a
*Lens tag*, not a proven identification — the proven content is the
census and its `42 × 4` factorization.)  213-native reading: at L4 the
doubling functor's associativity loss becomes *inhabited*, and its
inhabitants are exactly indexed by (octonion ×-atom) × (shifted
non-conjugate slot) — the tower's own `object1_not_surjective` moment,
with a finite signature `(42, 4, 168)`.

Kernel certification here is chunked (`decide` per `pairCount`; the full
`census = 168` in one `decide` stack-overflows the elaborator): this
file certifies the witness row's four structural facts cheaply.
Per-row certification `aCount a = 24` is measured feasible (∅-axiom,
~2 min kernel time per row) — the full 15-row ledger is the queued
follow-up, deliberately kept out of the always-built tree for build-time
discipline.  Roadmap: `research-notes/frontiers/divergence_conjecture_slate.md` S6.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionCensus

open E213.Lib.Math.Algebra.CayleyDickson.Levels.Sedenion

/-- Standard basis `e i` of the sedenions in the nested-CD encoding
    (bit `k` of `i` selects the `im`-slot at nesting level `k`). -/
def basis (i : Nat) : Sedenion :=
  let b0 := i % 2; let b1 := i / 2 % 2; let b2 := i / 4 % 2; let b3 := i / 8 % 2
  ⟨⟨⟨⟨(if b3==0 && b2==0 && b1==0 && b0==0 then 1 else 0),
      (if b3==0 && b2==0 && b1==0 && b0==1 then 1 else 0)⟩,
     ⟨(if b3==0 && b2==0 && b1==1 && b0==0 then 1 else 0),
      (if b3==0 && b2==0 && b1==1 && b0==1 then 1 else 0)⟩⟩,
    ⟨⟨(if b3==0 && b2==1 && b1==0 && b0==0 then 1 else 0),
      (if b3==0 && b2==1 && b1==0 && b0==1 then 1 else 0)⟩,
     ⟨(if b3==0 && b2==1 && b1==1 && b0==0 then 1 else 0),
      (if b3==0 && b2==1 && b1==1 && b0==1 then 1 else 0)⟩⟩⟩,
   ⟨⟨⟨(if b3==1 && b2==0 && b1==0 && b0==0 then 1 else 0),
      (if b3==1 && b2==0 && b1==0 && b0==1 then 1 else 0)⟩,
     ⟨(if b3==1 && b2==0 && b1==1 && b0==0 then 1 else 0),
      (if b3==1 && b2==0 && b1==1 && b0==1 then 1 else 0)⟩⟩,
    ⟨⟨(if b3==1 && b2==1 && b1==0 && b0==0 then 1 else 0),
      (if b3==1 && b2==1 && b1==0 && b0==1 then 1 else 0)⟩,
     ⟨(if b3==1 && b2==1 && b1==1 && b0==0 then 1 else 0),
      (if b3==1 && b2==1 && b1==1 && b0==1 then 1 else 0)⟩⟩⟩⟩

/-- Weld: the encoding matches the existing witness `zd_u = e₁ + e₁₀`. -/
theorem basis_weld_u : basis 1 + basis 10 = zd_u := by decide

/-- Weld: `zd_v = e₄ − e₁₅`. -/
theorem basis_weld_v : basis 4 + - basis 15 = zd_v := by decide

/-- Partner hits of the left pair `(a,b)` at the right pair `(c,d)`:
    counts `(e_a+e_b)(e_c+e_d) = 0` and `(e_a+e_b)(e_c−e_d) = 0`. -/
def hits (a b c d : Nat) : Nat :=
  (if (basis a + basis b) * (basis c + basis d) = 0 then 1 else 0) +
  (if (basis a + basis b) * (basis c + - basis d) = 0 then 1 else 0)

/-- Partner count of the left pair `(a,b)` over all `1 ≤ c < d ≤ 15`. -/
def pairCount (a b : Nat) : Nat :=
  (List.range 16).foldl (fun n c =>
    if 1 ≤ c then
      (List.range 16).foldl (fun n d => if c < d then n + hits a b c d else n) n
    else n) 0

set_option maxRecDepth 100000

/-- ★ The witness pair `e₁ + e₁₀` has exactly **4** partners. -/
theorem witness_pair_count : pairCount 1 10 = 4 := by decide

/-- ★ Octonion-half pairs have NO partners (composition holds below L4):
    `e₁ + e₂` (both indices < 8) annihilates nothing. -/
theorem octonion_pair_count : pairCount 1 2 = 0 := by decide

/-- ★ The doubling unit `e₈` is excluded: `e₁ + e₈` has no partners. -/
theorem doubling_unit_excluded : pairCount 1 8 = 0 := by decide

/-- ★ The conjugate-index slot `b = a + 8` is excluded:
    `e₁ + e₉` has no partners. -/
theorem conjugate_slot_excluded : pairCount 1 9 = 0 := by decide

/-- ★★ The census signature at the witness row, bundled: partners exist
    exactly off the octonion half, off the doubling unit, and off the
    conjugate slot — and where they exist, there are exactly 4.
    (Full-table census `42 × 4 = 168` interpreter-verified; per-row
    kernel certification is the queued follow-up.) -/
theorem census_signature_row_one :
    pairCount 1 10 = 4 ∧ pairCount 1 2 = 0
    ∧ pairCount 1 8 = 0 ∧ pairCount 1 9 = 0 :=
  ⟨witness_pair_count, octonion_pair_count,
   doubling_unit_excluded, conjugate_slot_excluded⟩

end E213.Lib.Math.Algebra.CayleyDickson.Levels.SedenionCensus
