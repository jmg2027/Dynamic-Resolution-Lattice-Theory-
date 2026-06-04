import E213.Lens.LensCore
import E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot

/-!
# The modular-geodesic engine: a Raw-`Lens` whose view is the Stern-Brocot / Farey reading

The `Lens`-level engine behind the modular-geodesic cluster
(`theory/essays/p_orbit/the_modular_geodesic_lens.md`).  The residue's self-pointing, read by the **mediant**
Lens, lands on the Stern-Brocot / Farey vertices that the Markov tree, the convergents, and the
Lagrange/Markov spectrum are all built on.

  * `mediantLens : Lens (ℕ×ℕ)` — atoms `0/1`, `1/0`; `combine` = the mediant `(a,b)⊕(c,d)=(a+c,b+d)`.
  * `mediantLens.view : Raw → ℕ×ℕ` — Raw's self-reading as a Farey position (the geodesic's cutting
    sequence is the Raw tree; the fraction is where the path lands).
  * `mediantLens_view_reachable` — **the engine**: every `Raw` view is `SternBrocotReachable`, so the
    image of the Raw mediant-Lens is inside the Farey set the whole cluster is built on
    (`Mobius213SternBrocot.SternBrocotReachable`).

Scope (honest).  The inclusion is `range(view) ⊆ SternBrocotReachable`, not equality: `Raw.slash`
forbids self-mediants and arbitrary slash children are not unimodular-adjacent, so the view is neither
surjective onto the reachable set nor always coprime (e.g. `(3,3)` is a view but not coprime).  The
engine *feeds* the cluster; it does not exhaust it — and the unimodular floor (`W²=1`, adjacency) is a
property of the interval/path structure, not of arbitrary mediants.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeodesicLens

open E213.Theory (Raw)
open E213.Lens (Lens)
open E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot (SternBrocotReachable)

/-- The **modular-geodesic Lens**: the Raw-`Lens` whose two atoms are the Farey seeds `0/1` and `1/0`,
    and whose `combine` is the **mediant** `(a,b) ⊕ (c,d) = (a+c, b+d)`.  `mediantLens.view : Raw → ℕ×ℕ`
    is Raw's self-pointing recorded as a Stern-Brocot / Farey position — one geodesic on `ℍ/PSL(2,ℤ)`,
    its cutting sequence being the Raw tree. -/
def mediantLens : Lens (Nat × Nat) :=
  ⟨(0, 1), (1, 0), fun p q => (p.1 + q.1, p.2 + q.2)⟩

-- The engine computes: the seeds and the root mediant.
example : mediantLens.view Raw.a = (0, 1) := rfl
example : mediantLens.view Raw.b = (1, 0) := rfl

/-- The mediant `combine` is symmetric (componentwise `add_comm`), so `Raw.slash`'s direction-freedom
    (`a/b = b/a`) is respected and the Lens is well-defined on `Raw`. -/
theorem mediant_sym (u v : Nat × Nat) :
    mediantLens.combine u v = mediantLens.combine v u := by
  show (u.1 + v.1, u.2 + v.2) = (v.1 + u.1, v.2 + u.2)
  rw [Nat.add_comm u.1 v.1, Nat.add_comm u.2 v.2]

/-- The view of a `slash` is the **mediant** of the children's views — the Farey-sum step. -/
theorem mediantLens_view_slash (x y : Raw) (h : x ≠ y) :
    mediantLens.view (Raw.slash x y h)
      = ((mediantLens.view x).1 + (mediantLens.view y).1,
         (mediantLens.view x).2 + (mediantLens.view y).2) :=
  Raw.fold_slash mediantLens.base_a mediantLens.base_b mediantLens.combine mediant_sym x y h

example : mediantLens.view (Raw.slash Raw.a Raw.b (by decide)) = (1, 1) := by
  rw [mediantLens_view_slash]; rfl

/-- ★★★★★ **The engine**: every `Raw`, read by the modular-geodesic Lens, lands on a Stern-Brocot /
    Farey vertex — `mediantLens.view r ∈ SternBrocotReachable` for every `r`.  By `Raw.rec`: the atoms
    are the seeds `0/1`, `1/0`; `slash` is the mediant rule.  So the Farey set that `Mobius213SternBrocot`
    (and downstream the Markov tree, the convergents, the Lagrange/Markov spectrum) is built on is *fed*
    by the Raw mediant-Lens: the residue's self-pointing, read through the modular Lens, is exactly the
    cutting-sequence of a geodesic on `ℍ/PSL(2,ℤ)`. -/
theorem mediantLens_view_reachable (r : Raw) :
    SternBrocotReachable (mediantLens.view r) := by
  induction r using Raw.rec with
  | a => exact SternBrocotReachable.seedZero
  | b => exact SternBrocotReachable.seedInf
  | slash x y h ihx ihy =>
      rw [mediantLens_view_slash x y h]
      exact SternBrocotReachable.mediant ihx ihy

end E213.Lib.Math.NumberSystems.Real213.ModularGeodesicLens
