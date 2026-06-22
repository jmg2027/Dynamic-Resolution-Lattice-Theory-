import E213.Lib.Math.Algebra.CassiniUnimodular
import E213.Lib.Math.NumberSystems.Real213.Markov.SternBrocotMarkov

/-!
# The Markov orbit's Cassini determinant is conserved — `det₂ = 1` is the Cassini multiplier `q = 1`

This bridges the two sub-domains of the unimodular family (`UnimodularSynthesis`): the Markov /
Stern-Brocot `SL₂(ℤ)` tree and the golden / Fibonacci Cassini conservation
(`CassiniUnimodular`). They are one law.

Fix a unimodular `M_l` (`det₂ M_l = 1`) and look at its left-multiplication orbit on any seed
`M_r`; read the `c`-entry at each step, `s(k) = (M_l^k · M_r).c`. By the Cayley–Hamilton Vieta
recurrence (`SternBrocotMarkov.markoff_vieta`, which needs exactly `det₂ M_l = 1`) this sequence
obeys the 2nd-order recurrence `s(k+2) = tr(M_l)·s(k+1) − 1·s(k)` — multiplier `q = det₂ M_l = 1`.
So by the parametric Cassini law (`CassiniUnimodular.det_step`, multiplier `q`) the sequence's
**Cassini determinant is conserved** (`det s (n+1) = det s n`, `det s n = det s 0`), the *same*
`q = 1` conservation as the golden Cassini (`CassiniUnimodular.det_golden`).

The point: `det₂ = 1` (the `SL₂` unimodular invariant of the Stern-Brocot / Markov tree) **is**
the Cassini multiplier `q` of the matrix-entry recurrence. The two unimodular phenomena are one.

Companion essay: `theory/essays/synthesis/unimodular_invariant.md`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Markov.MarkovCassiniUnimodular

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul)
open E213.Lib.Math.NumberSystems.Real213.Markov.SternBrocotMarkov
  (det2 markoff_vieta mInterval mInterval_det genL)
open E213.Lib.Math.Algebra.CassiniUnimodular (det det_step det_closed qpow qpow_one)

/-- The left-multiplication orbit of `M_l` on a seed `M_r`. -/
def morbit (Ml Mr : Mat2) : Nat → Mat2
  | 0 => Mr
  | n + 1 => mul Ml (morbit Ml Mr n)

/-- The `c`-entry read off the orbit — the Markov matrix-entry sequence. -/
def cval (Ml Mr : Mat2) (n : Nat) : Int := (morbit Ml Mr n).c

/-- ★★ **The orbit's `c`-entries obey a `q = 1` recurrence.**  `s(n+2) = tr(M_l)·s(n+1) − 1·s(n)`,
    the Cayley–Hamilton Vieta recurrence whose multiplier is `det₂ M_l = 1`. -/
theorem cval_rec (Ml Mr : Mat2) (hdet : det2 Ml = 1) (n : Nat) :
    cval Ml Mr (n + 2) = (Ml.a + Ml.d) * cval Ml Mr (n + 1) - 1 * cval Ml Mr n := by
  show (mul Ml (mul Ml (morbit Ml Mr n))).c
     = (Ml.a + Ml.d) * (mul Ml (morbit Ml Mr n)).c - 1 * (morbit Ml Mr n).c
  rw [markoff_vieta Ml (morbit Ml Mr n) hdet, Int.one_mul]

/-- ★★★ **The Markov orbit's Cassini determinant is conserved** (`q = 1`).  For any unimodular
    `M_l`, the Cassini determinant of the orbit's `c`-entry sequence does not change step to step
    — the same conservation as the golden Cassini, because `det₂ M_l = 1` is the multiplier. -/
theorem markov_orbit_cassini_step (Ml Mr : Mat2) (hdet : det2 Ml = 1) (n : Nat) :
    det (cval Ml Mr) (n + 1) = det (cval Ml Mr) n := by
  have h := det_step (Ml.a + Ml.d) 1 (cval Ml Mr) (cval_rec Ml Mr hdet) n
  rw [Int.one_mul] at h
  exact h

/-- ★★★ **Closed form: the Cassini determinant is constant along the whole orbit.**
    `det s n = det s 0` for every `n` (multiplier `q = 1`, so `qⁿ = 1`). -/
theorem markov_orbit_cassini_const (Ml Mr : Mat2) (hdet : det2 Ml = 1) (n : Nat) :
    det (cval Ml Mr) n = det (cval Ml Mr) 0 := by
  have h := det_closed (Ml.a + Ml.d) 1 (cval Ml Mr) (cval_rec Ml Mr hdet) n
  rw [qpow_one, Int.one_mul] at h
  exact h

/-- ★ **Concrete instance** at the Stern-Brocot generator `M_l = genL = [[2,1],[1,1]]`
    (`det₂ = 1`): the `c`-entry orbit's Cassini determinant is conserved. -/
theorem genL_orbit_cassini_const (Mr : Mat2) (n : Nat) :
    det (cval genL Mr) n = det (cval genL Mr) 0 :=
  markov_orbit_cassini_const genL Mr (mInterval_det []).1 n

end E213.Lib.Math.NumberSystems.Real213.Markov.MarkovCassiniUnimodular
