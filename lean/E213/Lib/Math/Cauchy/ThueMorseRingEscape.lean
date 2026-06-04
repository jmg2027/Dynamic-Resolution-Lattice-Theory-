import E213.Lib.Math.Cauchy.ThueMorseAperiodic
import E213.Lib.Math.Cauchy.PolyDepthMonotone

/-!
# The popcount counter has no finite difference-depth (∅-axiom)

The digit counter `s2 = popcount`, read off the automaton that emits Thue–Morse, is **unbounded**
yet returns to its minimum `1` at every power of two, hence **not eventually monotone**
(`ThueMorseAperiodic.s2_not_eventually_monotone`).  Composed with the bridge
`PolyDepthMonotone.polyDepthZ_evMono` (a finite-Δ-depth integer sequence is eventually monotone),
this closes the ring-escape as a genuine theorem:

> `s2Z_not_polyDepthZ : ¬ ∃ d, polyDepthZ d s2Z`

— the automatic sequence's counter sits **outside** the finite-difference generating ring, while
its bounded `{0,1}` readout `tm` is the dense non-holonomic witness.  The narrative
("readout escapes the machine, counter escapes the ring") is now ∅-axiom on both halves.
-/

namespace E213.Lib.Math.Cauchy.ThueMorseRingEscape

open E213.Lib.Math.Cauchy.ThueMorseAperiodic
open E213.Lib.Math.Cauchy.PolyDepthMonotone
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ)
open E213.Meta.Int213.Order (le_of_ofNat_le)

/-- The `Int` embedding of the binary digit-sum (popcount). -/
def s2Z (n : Nat) : Int := Int.ofNat (s2 n)

/-- `s2` is not eventually non-decreasing (transport of `s2_not_eventually_monotone`). -/
theorem s2Z_not_monoFrom (N : Nat) : ¬ MonoFromZ N s2Z := by
  intro hmono
  exact s2_not_eventually_monotone ⟨N, fun m n hNm hmn => le_of_ofNat_le (hmono m n hNm hmn)⟩

/-- `s2` is not eventually non-increasing: a non-increasing tail would bound it, but
    `s2 (ones k) = k` is unbounded. -/
theorem s2Z_not_antiFrom (N : Nat) : ¬ AntiFromZ N s2Z := by
  intro hanti
  have hge : N ≤ ones (N + s2 N + 1) :=
    Nat.le_trans (Nat.le_add_right N (s2 N + 1)) (ones_ge (N + s2 N + 1))
  have hle : s2Z (ones (N + s2 N + 1)) ≤ s2Z N :=
    hanti N (ones (N + s2 N + 1)) (Nat.le_refl N) hge
  have hnat : s2 (ones (N + s2 N + 1)) ≤ s2 N := le_of_ofNat_le hle
  rw [s2_ones] at hnat
  exact Nat.not_succ_le_self (s2 N)
    (Nat.le_trans (Nat.succ_le_succ (Nat.le_add_left (s2 N) N)) hnat)

/-- ★★★ **The popcount counter has no finite difference-depth.**  `s2Z` (the `Int` embedding of
    the binary digit-sum) is not `polyDepthZ d` for any `d`: it is unbounded yet not eventually
    monotone, so the finite-depth ⟹ eventually-monotone bridge rules out every depth.  The
    automatic sequence's counter escapes the difference-Lens generating ring. -/
theorem s2Z_not_polyDepthZ : ¬ ∃ d, polyDepthZ d s2Z := by
  rintro ⟨d, hpd⟩
  rcases polyDepthZ_evMono d s2Z hpd with ⟨N, hmono⟩ | ⟨N, hanti⟩
  · exact s2Z_not_monoFrom N hmono
  · exact s2Z_not_antiFrom N hanti

end E213.Lib.Math.Cauchy.ThueMorseRingEscape
