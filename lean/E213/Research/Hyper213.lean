import E213.Firmware.Raw

/-!
# Research.Hyper213: Hyperreal-like 의 framework-internal type

User insight: 초실수 가 213 에 자연 capture.  Cauchy 의 modulus
요구 *없이* sequence 만 — 그 위 *cofinite equivalence* 로
"infinitesimal + finite + infinite" 의 자연 algebra.

## 정의

`Hyper213 := Nat → Raw` (raw sequence, no modulus).
`Hyper213.cofiniteEquiv xs ys := ∃ N, ∀ n ≥ N, xs n = ys n`.

## 의의

- Cauchy 보다 *느슨* 한 equivalence — Cauchy modulus 없 이 도
  의미 있는 algebra.
- Standard Cauchy 는 *strict subset* — Cauchy ∧ same limit
  → cofinite equiv (after limit reaches stability).
- Cofinite equiv 가 reflexive, symmetric, transitive — true
  equivalence.

## 의 미

ZFC 의 ℝ 가 *power set 기반* (Dedekind cut = 임의 subset of ℚ).
213 의 Real213 = *constructive Cauchy*.  Hyper213 = sequence
의 *cofinite quotient* — ZFC 의 free ultrafilter (NSA) 보 다 약
하 지 만 framework-internal.

대 부 분 의 *exotic* number systems (hyperreals, surreals 등)
가 sequence 또 는 tree structure 의 quotient — 213 framework
가 자연 capture.

오 직 *arbitrary subset* (power set) 만 framework 의 거부.
-/

namespace E213.Research.Hyper213

open E213.Firmware

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
  have hN1 : n ≥ N1 := Nat.le_trans (Nat.le_max_left N1 N2) hn
  have hN2 : n ≥ N2 := Nat.le_trans (Nat.le_max_right N1 N2) hn
  exact (h1 n hN1).trans (h2 n hN2)

end E213.Research.Hyper213

namespace E213.Research.Hyper213

open E213.Firmware

/-- Constant hyperreal embedding: each Raw r → constant sequence. -/
def constHyper (r : Raw) : Hyper213 := fun _ => r

/-- Constant Hyper213 의 cofinite equivalence iff Raw equality. -/
theorem const_equiv_iff (r r' : Raw) :
    cofiniteEquiv (constHyper r) (constHyper r') ↔ r = r' := by
  refine ⟨?_, ?_⟩
  · rintro ⟨N, h⟩
    exact h N (Nat.le_refl N)
  · intro h; rw [h]; exact cofinite_refl _

end E213.Research.Hyper213
