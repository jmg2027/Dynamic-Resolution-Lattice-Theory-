import E213.Lib.Math.Real213.Mobius213Equiv
import E213.Meta.Tactic.NatHelper

/-!
# Mobius213SternBrocot — Stern-Brocot reachable equivalence on cuts

Closure of the two Möbius seeds `(0, 1)` and `(1, 0)` under the
mediant operation (a, b) ⊕ (c, d) = (a+c, b+d).  Equivalent to
the orbit of the seeds under the L+R monoid action — where
L = [[1,0],[1,1]] and R = [[1,1],[0,1]] are the standard SL₂(ℤ)
generators whose composite R·L = [[2,1],[1,1]] is the 213
Möbius matrix P (`Lib/Math/Mobius213.lean`).

Every coprime (m, k) ∈ ℕ × ℕ appears (uniquely) in the
Stern-Brocot tree, so the mediant-closure equality
`sternBrocotEq` is strictly stronger than the P-orbit-only
`mobiusEq` (`Mobius213Equiv.lean`).

  · `mobiusEq` (P-orbit, two thin Pell chains)
  · `sternBrocotEq` (mediant closure of seeds, all coprime pairs)
  · `cutEq` (pointwise on all of ℕ × ℕ)

The chain `cutEq ⇒ sternBrocotEq ⇒ mobiusEq` holds
unconditionally; the converses require additional structure
(scale-invariance for `sternBrocotEq ⇒ cutEq` since cuts on
non-coprime (m, k) factor through the coprime reduction; and a
Pell-coverage argument for `mobiusEq ⇒ sternBrocotEq`, which
fails for general cuts).

## What this file delivers

  · `SternBrocotReachable (m, k)` — inductive closure of
    {(0,1), (1,0)} under mediant
  · Concrete L0–L2 witnesses: (1,1), (1,2), (2,1), (1,3), (2,3),
    (3,2), (3,1) — every coprime pair with max ≤ 3
  · `sternBrocotEq cx cy` — agreement on all reachable (m, k)
  · refl / symm / trans (equivalence-relation laws)
  · `sternBrocotEq_of_cutEq` — pointwise ⇒ Stern-Brocot
  · `mobiusEq_of_sternBrocotEq_at_seeds` — the two P-seeds are
    reachable, so `sternBrocotEq` constrains both seed cells
    immediately (one half of the P-orbit inclusion bridge; the
    full ∀n inclusion requires a mediant identity for `Pstep`
    proved separately)

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Real213.Mobius213SternBrocot

open E213.Lib.Math.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.Real213.Mobius213Equiv (Pstep Pseq seedZero seedInf mobiusEq)
open E213.Tactic.NatHelper (add_swap_two_mul)

/-! ## §1 — SternBrocotReachable inductive predicate -/

/-- **SternBrocotReachable**: closure of the seeds `(0, 1)` and
    `(1, 0)` under the mediant `(a, b) ⊕ (c, d) := (a+c, b+d)`.
    Every coprime pair appears (uniquely) at some finite depth
    (the Stern-Brocot tree node theorem). -/
inductive SternBrocotReachable : Nat × Nat → Prop where
  | seedZero : SternBrocotReachable (0, 1)
  | seedInf  : SternBrocotReachable (1, 0)
  | mediant {a b c d : Nat} :
      SternBrocotReachable (a, b) →
      SternBrocotReachable (c, d) →
      SternBrocotReachable (a + c, b + d)

/-! ## §2 — Initial coprime witnesses (Stern-Brocot levels 1–2) -/

/-- (1, 1) = (0+1, 1+0), the root mediant. -/
theorem reachable_1_1 : SternBrocotReachable (1, 1) :=
  .mediant .seedZero .seedInf

/-- (1, 2) = (0+1, 1+1), left child of root. -/
theorem reachable_1_2 : SternBrocotReachable (1, 2) :=
  .mediant .seedZero reachable_1_1

/-- (2, 1) = (1+1, 1+0), right child of root. -/
theorem reachable_2_1 : SternBrocotReachable (2, 1) :=
  .mediant reachable_1_1 .seedInf

/-- (1, 3) = (0+1, 1+2), left-left grandchild. -/
theorem reachable_1_3 : SternBrocotReachable (1, 3) :=
  .mediant .seedZero reachable_1_2

/-- (2, 3) = (1+1, 2+1), left-right grandchild. -/
theorem reachable_2_3 : SternBrocotReachable (2, 3) :=
  .mediant reachable_1_2 reachable_1_1

/-- (3, 2) = (2+1, 1+1), right-left grandchild — the (NS, NT)
    atomicity pair reached at depth 3. -/
theorem reachable_3_2 : SternBrocotReachable (3, 2) :=
  .mediant reachable_2_1 reachable_1_1

/-- (3, 1) = (2+1, 1+0), right-right grandchild. -/
theorem reachable_3_1 : SternBrocotReachable (3, 1) :=
  .mediant reachable_2_1 .seedInf

/-! ## §3 — sternBrocotEq: agreement on every reachable (m, k) -/

/-- **sternBrocotEq**: cx, cy agree on every Stern-Brocot
    reachable (m, k).  Strictly stronger than `mobiusEq`
    (which checks only the P-orbit Pell chains); weaker than
    `cutEq` (which checks all of ℕ × ℕ pointwise, including
    non-coprime pairs not in the Stern-Brocot tree). -/
def sternBrocotEq (cx cy : Nat → Nat → Bool) : Prop :=
  ∀ m k, SternBrocotReachable (m, k) → cx m k = cy m k

/-! ## §4 — sternBrocotEq is an equivalence relation -/

/-- sternBrocotEq reflexivity. -/
theorem sternBrocotEq_refl (c : Nat → Nat → Bool) : sternBrocotEq c c :=
  fun _ _ _ => rfl

/-- sternBrocotEq symmetry. -/
theorem sternBrocotEq_symm (cx cy : Nat → Nat → Bool) :
    sternBrocotEq cx cy → sternBrocotEq cy cx :=
  fun h m k hr => (h m k hr).symm

/-- sternBrocotEq transitivity. -/
theorem sternBrocotEq_trans (cx cy cz : Nat → Nat → Bool) :
    sternBrocotEq cx cy → sternBrocotEq cy cz → sternBrocotEq cx cz :=
  fun h1 h2 m k hr => (h1 m k hr).trans (h2 m k hr)

/-! ## §5 — Forward bridge: cutEq ⇒ sternBrocotEq -/

/-- ★★★ **Forward direction**: pointwise equality on all
    `(m, k)` implies agreement on every Stern-Brocot reachable
    pair.  Trivial reachability-blind specialisation. -/
theorem sternBrocotEq_of_cutEq (cx cy : Nat → Nat → Bool) :
    cutEq cx cy → sternBrocotEq cx cy :=
  fun h m k _ => h m k

/-! ## §6 — Reachability of the two P-seed cells -/

/-- The two Möbius P-seeds `(0, 1)` and `(1, 0)` are the
    Stern-Brocot constructors; reachability is by `seedZero`
    and `seedInf` directly. -/
theorem seedZero_reachable : SternBrocotReachable (0, 1) := .seedZero

/-- See `seedZero_reachable`. -/
theorem seedInf_reachable : SternBrocotReachable (1, 0) := .seedInf

/-! ## §7 — Pell-convergent inclusion (Pseq → SternBrocotReachable)

The two P-orbits trace diagonal paths in the Stern-Brocot tree
via mediant identities for `Pstep`.  The cross-orbit relation

  `(Pseq seedInf n).1 = (Pseq seedZero n).1 + (Pseq seedZero n).2`
  `(Pseq seedInf n).2 = (Pseq seedZero n).1`

is the only Nat-arithmetic ingredient — proved as
`Pseq_seedInf_components` by joint induction.  Joint reachability
of both P-orbits then follows by induction using the constructor
`SternBrocotReachable.mediant` directly. -/

/-- Helper: `2·(a + b) + a = (2·a + b) + (a + b)`.  The
    arithmetic certificate that `Pseq seedInf` advances by the
    same Pstep-Mediant identity as `Pseq seedZero`. -/
private theorem two_mul_add_swap (a b : Nat) :
    2 * (a + b) + a = (2 * a + b) + (a + b) := by
  rw [Nat.mul_add, Nat.add_assoc (2*a) (2*b) a, Nat.add_assoc (2*a) b (a+b)]
  apply congrArg (2 * a + ·)
  rw [Nat.two_mul b, Nat.add_assoc b b a, Nat.add_comm b a]

/-- ★★ **Cross-orbit relation**: the seedInf P-orbit's components
    are determined by the seedZero P-orbit's components at the
    same depth.  Joint induction; only Nat-arithmetic step in the
    whole Pseq → SternBrocotReachable bridge. -/
theorem Pseq_seedInf_components (n : Nat) :
    (Pseq seedInf n).1 = (Pseq seedZero n).1 + (Pseq seedZero n).2
    ∧ (Pseq seedInf n).2 = (Pseq seedZero n).1 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · show 2 * (Pseq seedInf k).1 + (Pseq seedInf k).2
         = (2 * (Pseq seedZero k).1 + (Pseq seedZero k).2)
           + ((Pseq seedZero k).1 + (Pseq seedZero k).2)
      rw [ih1, ih2]
      exact two_mul_add_swap _ _
    · show (Pseq seedInf k).1 + (Pseq seedInf k).2
         = 2 * (Pseq seedZero k).1 + (Pseq seedZero k).2
      rw [ih1, ih2]
      exact add_swap_two_mul _ _

/-- ★★★★★ **Joint P-orbit reachability**: every element of
    either P-orbit is Stern-Brocot reachable.  Joint induction:
    the inductive step uses the mediant identities

      `Pseq seedZero (k+1) = mediant(Pseq seedZero k, Pseq seedInf k)`
      `Pseq seedInf  (k+1) = mediant(Pseq seedZero (k+1), Pseq seedInf k)`

    whose component equalities reduce, via `Pseq_seedInf_components`,
    to the two Nat-arithmetic helpers `add_swap_two_mul` and
    `two_mul_add_swap`. -/
theorem Pseq_reachable (n : Nat) :
    SternBrocotReachable (Pseq seedZero n)
    ∧ SternBrocotReachable (Pseq seedInf n) := by
  induction n with
  | zero => exact ⟨.seedZero, .seedInf⟩
  | succ k ih =>
    obtain ⟨hz, hi⟩ := ih
    obtain ⟨hc1, hc2⟩ := Pseq_seedInf_components k
    have hz' : SternBrocotReachable (Pseq seedZero (k+1)) := by
      show SternBrocotReachable
        (2 * (Pseq seedZero k).1 + (Pseq seedZero k).2,
         (Pseq seedZero k).1 + (Pseq seedZero k).2)
      have target_eq :
          ((Pseq seedZero k).1 + (Pseq seedInf k).1,
           (Pseq seedZero k).2 + (Pseq seedInf k).2)
          = (2 * (Pseq seedZero k).1 + (Pseq seedZero k).2,
             (Pseq seedZero k).1 + (Pseq seedZero k).2) := by
        rw [hc1, hc2]
        apply Prod.ext
        · show (Pseq seedZero k).1 + ((Pseq seedZero k).1 + (Pseq seedZero k).2)
             = 2 * (Pseq seedZero k).1 + (Pseq seedZero k).2
          rw [← Nat.add_assoc, ← Nat.two_mul]
        · exact Nat.add_comm _ _
      rw [← target_eq]
      exact .mediant hz hi
    have hi' : SternBrocotReachable (Pseq seedInf (k+1)) := by
      show SternBrocotReachable
        (2 * (Pseq seedInf k).1 + (Pseq seedInf k).2,
         (Pseq seedInf k).1 + (Pseq seedInf k).2)
      have target_eq :
          ((Pseq seedZero (k+1)).1 + (Pseq seedInf k).1,
           (Pseq seedZero (k+1)).2 + (Pseq seedInf k).2)
          = (2 * (Pseq seedInf k).1 + (Pseq seedInf k).2,
             (Pseq seedInf k).1 + (Pseq seedInf k).2) := by
        show ((2 * (Pseq seedZero k).1 + (Pseq seedZero k).2) + (Pseq seedInf k).1,
              ((Pseq seedZero k).1 + (Pseq seedZero k).2) + (Pseq seedInf k).2)
            = (2 * (Pseq seedInf k).1 + (Pseq seedInf k).2,
               (Pseq seedInf k).1 + (Pseq seedInf k).2)
        rw [hc1, hc2]
        apply Prod.ext
        · exact (two_mul_add_swap _ _).symm
        · rfl
      rw [← target_eq]
      exact .mediant hz' hi
    exact ⟨hz', hi'⟩

/-! ## §8 — Bridge to the weaker P-orbit equivalence -/

/-- ★★★ **Forward bridge sternBrocotEq → mobiusEq**: Stern-Brocot
    agreement at every reachable pair implies P-orbit agreement,
    since both P-orbits are sub-paths of the Stern-Brocot tree
    (by `Pseq_reachable`).  Together with `sternBrocotEq_of_cutEq`
    this realises the chain `cutEq ⇒ sternBrocotEq ⇒ mobiusEq`. -/
theorem mobiusEq_of_sternBrocotEq (cx cy : Nat → Nat → Bool) :
    sternBrocotEq cx cy → mobiusEq cx cy := by
  intro h n
  obtain ⟨hz, hi⟩ := Pseq_reachable n
  exact ⟨h (Pseq seedZero n).1 (Pseq seedZero n).2 hz,
         h (Pseq seedInf  n).1 (Pseq seedInf  n).2 hi⟩

/-! ## §9 — Full coverage of ℕ × ℕ \ {(0, 0)}

The mediant closure of {(0, 1), (1, 0)} reaches every non-trivial
pair: applying `.mediant _ .seedInf` extends the first component
by 1, and `.mediant _ .seedZero` extends the second.  Combined
with the two seeds (m + k = 1), this gives `SternBrocotReachable`
for every (m, k) with m + k ≥ 1.

The boundary (0, 0) is excluded by construction — it is not in
the mediant closure of `(0, 1)` and `(1, 0)`. -/

/-- Extend the first component by 1 via mediant with `seedInf`. -/
theorem reachable_succ_fst {m k : Nat} (h : SternBrocotReachable (m, k)) :
    SternBrocotReachable (m + 1, k) :=
  .mediant h .seedInf

/-- Extend the second component by 1 via mediant with `seedZero`. -/
theorem reachable_succ_snd {m k : Nat} (h : SternBrocotReachable (m, k)) :
    SternBrocotReachable (m, k + 1) :=
  .mediant h .seedZero

/-- The (0, k+1) column is reachable for every `k`. -/
theorem reachable_zero_succ : ∀ k, SternBrocotReachable (0, k + 1)
  | 0     => .seedZero
  | k + 1 => reachable_succ_snd (reachable_zero_succ k)

/-- The (m+1, 0) row is reachable for every `m`. -/
theorem reachable_succ_zero : ∀ m, SternBrocotReachable (m + 1, 0)
  | 0     => .seedInf
  | m + 1 => reachable_succ_fst (reachable_succ_zero m)

/-- The (1, k+1) row is reachable for every `k`. -/
theorem reachable_one_succ : ∀ k, SternBrocotReachable (1, k + 1)
  | 0     => reachable_1_1
  | k + 1 => reachable_succ_snd (reachable_one_succ k)

/-- Auxiliary: from `SR (1, k+1)`, extend the first component
    to any `m + 1`.  Single-Nat recursion on `m` keeps the proof
    structurally pure (avoiding `Nat × Nat` brec compilation). -/
private theorem reachable_succ_succ_aux :
    ∀ (m : Nat) {k : Nat},
    SternBrocotReachable (1, k + 1) → SternBrocotReachable (m + 1, k + 1)
  | 0,     _, h => h
  | m + 1, _, h => reachable_succ_fst (reachable_succ_succ_aux m h)

/-- The interior (m+1, k+1) cell is reachable for every `m, k`. -/
theorem reachable_succ_succ (m k : Nat) :
    SternBrocotReachable (m + 1, k + 1) :=
  reachable_succ_succ_aux m (reachable_one_succ k)

/-- ★★★★★ **Full coverage**: every (m, k) ∈ ℕ × ℕ with
    m + k ≥ 1 is Stern-Brocot reachable.  Case split: (0, k+1)
    via `reachable_zero_succ`, (m+1, 0) via `reachable_succ_zero`,
    (m+1, k+1) via `reachable_succ_succ`.  The boundary `(0, 0)`
    is excluded — not in the mediant closure of the two seeds. -/
theorem reachable_of_pos : ∀ (m k : Nat), 1 ≤ m + k → SternBrocotReachable (m, k)
  | 0,     0,     h => absurd h (Nat.not_succ_le_zero 0)
  | 0,     k + 1, _ => reachable_zero_succ k
  | m + 1, 0,     _ => reachable_succ_zero m
  | m + 1, k + 1, _ => reachable_succ_succ m k

/-! ## §10 — Backward bridge: sternBrocotEq ⇒ cutEq (mod (0, 0)) -/

/-- ★★★★★★ **Backward bridge**: Stern-Brocot agreement plus a
    `(0, 0)`-side condition implies full pointwise cut equality.
    The side condition at `(0, 0)` is unavoidable in general —
    `SternBrocotReachable` is closed under mediant operations
    starting from `(0, 1)` and `(1, 0)`, so it cannot reach
    `(0, 0)`.  For cut-framework cuts such as `constCut a N`,
    the value at `(0, 0)` is canonically `true` (since
    `a * 0 ≤ N * 0` for all `a, N`), so the side condition is
    automatic in practice. -/
theorem cutEq_of_sternBrocotEq (cx cy : Nat → Nat → Bool)
    (h : sternBrocotEq cx cy) (h00 : cx 0 0 = cy 0 0) :
    cutEq cx cy :=
  fun m k => match m, k with
    | 0,     0     => h00
    | 0,     k + 1 => h 0 (k + 1) (reachable_zero_succ k)
    | m + 1, 0     => h (m + 1) 0 (reachable_succ_zero m)
    | m + 1, k + 1 => h (m + 1) (k + 1) (reachable_succ_succ m k)

/-- ★★★★★ **Equivalence**: `cutEq` is `sternBrocotEq` plus the
    `(0, 0)` side condition.  Closes the canonical-equivalence
    conjecture for cuts on `Nat → Nat → Bool` (modulo the single
    boundary value at `(0, 0)`). -/
theorem cutEq_iff_sternBrocotEq_and_zero (cx cy : Nat → Nat → Bool) :
    cutEq cx cy ↔ sternBrocotEq cx cy ∧ cx 0 0 = cy 0 0 :=
  ⟨fun h => ⟨sternBrocotEq_of_cutEq cx cy h, h 0 0⟩,
   fun ⟨hSB, h00⟩ => cutEq_of_sternBrocotEq cx cy hSB h00⟩

end E213.Lib.Math.Real213.Mobius213SternBrocot
