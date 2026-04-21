import E213.Infinity.Countable
import E213.Infinity.LensCardinality
import E213.Meta.LensCatalog
import E213.Prelude

/-!
# Infinity.BTower: dual tower covering the negative ℤ-side

`rawTower` from `Countable` covers signed-view `{-1, 0, 1, …}`
via right-leaning slashes of `a`.  The dual `bTower` covers
`{-n, …, 0}` via slashes of `b`, completing
`signedLens : Raw → ℤ` surjectivity onto all of `ℤ`.

Structure: `bTree 0 = slash a b` (canonical; view `= 0`),
`bTree (n+1) = slash b (bTree n)` (canonical since
`cmp b (slash _ _) = lt`; view adds `-1`).  So `view(bTree n)
= -n`.
-/

namespace E213.Firmware.Internal

/-- Dual (b-leaning) Tree tower. -/
def bTree : Nat → Tree
  | 0     => Tree.slash Tree.a Tree.b
  | n + 1 => Tree.slash Tree.b (bTree n)

theorem cmp_b_bTree : ∀ n, Tree.cmp Tree.b (bTree n) = .lt := by
  intro n; cases n with
  | zero => rfl
  | succ m => rfl

theorem bTree_canonical :
    ∀ n, (bTree n).canonical = true := by
  intro n; induction n with
  | zero => rfl
  | succ m ih =>
      show ((Tree.b.canonical && (bTree m).canonical)
            && match Tree.cmp Tree.b (bTree m)
                 with | .lt => true | _ => false) = true
      rw [cmp_b_bTree, ih]
      rfl

theorem bTree_signed :
    ∀ n, Tree.fold (1 : Int) (-1) (· + ·) (bTree n) = -(n : Int) := by
  intro n; induction n with
  | zero => rfl
  | succ m ih =>
      show (-1 : Int) + Tree.fold (1 : Int) (-1) (· + ·) (bTree m)
             = -(m + 1 : Int)
      rw [ih]; push_cast; omega

end E213.Firmware.Internal

namespace E213.Infinity

open E213.Firmware E213.Firmware.Internal E213.Hypervisor E213.Meta

/-- b-tower as Raw. -/
def rawBTower (n : Nat) : Raw := ⟨bTree n, bTree_canonical n⟩

theorem rawBTower_signed (n : Nat) :
    signedLens.view (rawBTower n) = -(n : Int) := by
  show Raw.fold (1 : Int) (-1) (· + ·) (rawBTower n) = -(n : Int)
  exact bTree_signed n

/-- **signedLens image covers `{z : ℤ | z ≤ 0}`** via the
    b-tower.  Combined with `signedLens_image_ge_neg_one`
    (`rawTower`), the union `rawTower ∪ rawBTower` exhausts
    all of `ℤ`. -/
theorem signedLens_image_le_zero :
    ∀ z : Int, z ≤ 0 → ∃ r : Raw, signedLens.view r = z := by
  intro z hz
  have ⟨n, hn⟩ : ∃ n : Nat, z = -(n : Int) := by
    refine ⟨(-z).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; omega
  refine ⟨rawBTower n, ?_⟩
  rw [rawBTower_signed, hn]

/-- **signedLens is surjective onto `ℤ`.**  For every integer
    `z`, either `z ≥ -1` (use `rawTower`) or `z ≤ 0` (use
    `rawBTower`).  The two cases overlap at `z ∈ {-1, 0}`
    which is fine for surjectivity. -/
theorem signedLens_surjective : Function.Surjective signedLens.view := by
  intro z
  by_cases h : z ≤ 0
  · exact signedLens_image_le_zero z h
  · exact signedLens_image_ge_neg_one z (by omega)

/-- **signedLens image is unbounded below.**  Symmetric to
    `signedLens_unbounded_above`. -/
theorem signedLens_unbounded_below :
    ∀ N : Nat, ∃ r : Raw, signedLens.view r ≤ -(N : Int) := by
  intro N
  obtain ⟨r, hr⟩ := signedLens_image_le_zero (-(N : Int)) (by omega)
  exact ⟨r, by rw [hr]; exact Int.le_refl _⟩

end E213.Infinity
