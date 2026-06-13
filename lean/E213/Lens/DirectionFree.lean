import E213.Lens.LensCore

/-!
# Direction-freedom is forced for residue-native readings

`Raw.slash` is direction-free: `x / y = y / x` (`Raw.slash_comm`, the third axiom clause).  A `Lens`
whose `view` is a *slash homomorphism* — one sending a slash to the `combine` of its children's views
(the conclusion of `Raw.fold_slash`) — must therefore have a `combine` that is **symmetric on its
image**.  So a residue-native (homomorphic) reading cannot break direction-freedom: any
orientation-dependent reading, whose combine is non-symmetric on its image, is **not** a Raw-`Lens` —
it lives on the oriented free monoid above the residue.

This is the foundation behind the slope/size asymmetry of the Markov tree
(`Real213/Markov/SternBrocotMarkov` §31): the mediant (slope) combine is commutative, so the slope reading is
a genuine Raw-`Lens`; the Markov size combine is the non-commutative matrix product, so it is not, and
the size reading lives one structural level above the direction-free residue.
-/

namespace E213.Lens.DirectionFree

open E213.Theory E213.Lens

/-- ★★★★★ **Direction-freedom forces combine-symmetry on the image.**  If a Lens's `view` is a slash
    homomorphism — `view (x / y) = combine (view x) (view y)` for all distinct `x, y` — then its
    `combine` is symmetric on the image, because `x / y = y / x` (`Raw.slash_comm`).

    Contrapositive: a `combine` that is non-symmetric on its image *cannot* give a homomorphic
    Raw-`Lens`.  Orientation-dependent (non-commutative) readings escape the residue. -/
theorem combine_sym_on_image_of_homomorphism {α : Type} (L : Lens α)
    (hfs : ∀ (x y : Raw) (h : x ≠ y),
      L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y))
    (x y : Raw) (h : x ≠ y) :
    L.combine (L.view x) (L.view y) = L.combine (L.view y) (L.view x) := by
  have h1 := hfs x y h
  have h2 := hfs y x (Ne.symm h)
  rw [Raw.slash_comm x y h, h2] at h1
  exact h1.symm

end E213.Lens.DirectionFree
