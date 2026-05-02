import E213.Meta.UniversalLens.Nat3
import E213.Meta.UniversalLens.Q213_3

/-!
# Triple-codomain Universal Lens capstone

Bundles the four Universal Lenses now established by 213's
metatheory:

  | lens          | codomain                | depth | status            |
  | idLens        | Raw                      |  --   | trivial           |
  | expSumLens    | ℕ × ℕ                   |   2   | bit-pattern uniq  |
  | q213Lens      | Q213 × Q213             |   2   | via expSumNat     |
  | expSumLens3   | ℕ × ℕ × ℕ              |   3   | NEW (this commit) |
  | q213Lens3     | Q213 × Q213 × Q213      |   3   | NEW (this commit) |

Triple-codomain instances close part of HANDOFF Open Continuation #5
(Universal Lens at higher codomains).  The pattern generalises:
adding ANY component to a universal lens preserves universality, as
long as the existing components are unchanged in the combine
operator (separability of the catamorphism).
-/

namespace E213.Meta.UniversalLens.TripleCapstone

open E213.Meta.UniversalLens.Core (IsUniversal)

/-- ★★★★★★★★ Triple-codomain universality capstone.

  Four non-trivial universal lenses constructed in 213's metatheory:

    1. expSumLens : Lens (ℕ × ℕ)            — Open Problem #6 (ℕ²)
    2. q213Lens   : Lens (Q213²)             — Open Problem #6 (ℚ²)
    3. expSumLens3 : Lens (ℕ × ℕ × ℕ)      — NEW (this marathon)
    4. q213Lens3  : Lens (Q213 × Q213 × Q213) — NEW (this marathon)

  All four at ≤ {propext, Quot.sound}.  Each codomain extension
  preserves the bit-pattern injectivity of expSumNat. -/
theorem universal_lens_triple_capstone :
    IsUniversal E213.Meta.UniversalLens.Nat2.expSumLens
    ∧ IsUniversal E213.Meta.UniversalLens.Q213.q213Lens
    ∧ IsUniversal E213.Meta.UniversalLens.Nat3.expSumLens3
    ∧ IsUniversal E213.Meta.UniversalLens.Q213_3.q213Lens3 :=
  ⟨E213.Meta.UniversalLens.Nat2Inj.expSumLens_is_universal,
   E213.Meta.UniversalLens.Q213Inj.q213Lens_is_universal,
   E213.Meta.UniversalLens.Nat3.expSumLens3_is_universal,
   E213.Meta.UniversalLens.Q213_3.q213Lens3_is_universal⟩

end E213.Meta.UniversalLens.TripleCapstone
