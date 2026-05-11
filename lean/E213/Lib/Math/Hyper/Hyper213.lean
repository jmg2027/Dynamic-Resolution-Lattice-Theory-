import E213.Theory.Raw
import E213.Term.Tactic.Nat213

/-!
# Hyper213: Framework-internal type for a hyperreal-like structure

User insight: hyperreals are naturally captured in 213.  Sequences only —
*without* a Cauchy modulus — with *cofinite equivalence* on top give a
natural algebra of "infinitesimal + finite + infinite."

## Definition

`Hyper213 := Nat → Raw` (raw sequence, no modulus).
`Hyper213.cofiniteEquiv xs ys := ∃ N, ∀ n ≥ N, xs n = ys n`.

## Significance

- A *looser* equivalence than Cauchy — meaningful algebra even without
  a Cauchy modulus.
- Standard Cauchy is a *strict subset* — Cauchy ∧ same limit
  → cofinite equiv (after the limit reaches stability).
- Cofinite equiv is reflexive, symmetric, transitive — a true
  equivalence.

## Meaning

ℝ in ZFC is *power-set based* (Dedekind cut = arbitrary subset of ℚ).
Real213 in 213 = *constructive Cauchy*.  Hyper213 = the *cofinite
quotient* of sequences — weaker than ZFC's free ultrafilter (NSA) but
framework-internal.

Most *exotic* number systems (hyperreals, surreals, etc.) are quotients
of sequences or tree structures — naturally captured by the 213 framework.

Only *arbitrary subsets* (power sets) are rejected by the framework.
-/

namespace E213.Lib.Math.Hyper.Hyper213

open E213.Theory

/-- Hyperreal-like sequence (no modulus). -/
def Hyper213 : Type := Nat → Raw

/-- Cofinite equivalence: agree from some N onwards. -/
def cofiniteEquiv (xs ys : Hyper213) : Prop :=
  ∃ N, ∀ n, n ≥ N → xs n = ys n

theorem cofinite_refl (xs : Hyper213) : cofiniteEquiv xs xs :=
  ⟨0, fun _ _ => rfl⟩

theorem cofinite_symm (xs ys : Hyper213) :
    cofiniteEquiv xs ys → cofiniteEquiv ys xs := by
  rintro ⟨N, h⟩
  exact ⟨N, fun n hn => (h n hn).symm⟩

theorem cofinite_trans (xs ys zs : Hyper213) :
    cofiniteEquiv xs ys → cofiniteEquiv ys zs → cofiniteEquiv xs zs := by
  rintro ⟨N1, h1⟩ ⟨N2, h2⟩
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have hN1 : n ≥ N1 := Nat.le_trans (E213.Tactic.Nat213.le_max_left N1 N2) hn
  have hN2 : n ≥ N2 := Nat.le_trans (E213.Tactic.Nat213.le_max_right N1 N2) hn
  exact (h1 n hN1).trans (h2 n hN2)

end E213.Lib.Math.Hyper.Hyper213

namespace E213.Lib.Math.Hyper.Hyper213

open E213.Theory

/-- Constant hyperreal embedding: each Raw r → constant sequence. -/
def constHyper (r : Raw) : Hyper213 := fun _ => r

/-- Cofinite equivalence of constant Hyper213 iff Raw equality. -/
theorem const_equiv_iff (r r' : Raw) :
    cofiniteEquiv (constHyper r) (constHyper r') ↔ r = r' := by
  refine ⟨?_, ?_⟩
  · rintro ⟨N, h⟩
    exact h N (Nat.le_refl N)
  · intro h; rw [h]; exact cofinite_refl _

end E213.Lib.Math.Hyper.Hyper213
