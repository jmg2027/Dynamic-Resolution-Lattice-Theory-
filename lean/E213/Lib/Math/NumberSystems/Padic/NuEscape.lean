import E213.Lib.Math.NumberSystems.Padic.Foundation
import E213.Theory.Raw.API

/-!
# A p-adic integer is a residue escape (the νF bridge, 2-adic case)

The companion to the König νF bridge (`Lib/Math/Combinatorics/KonigConditional.lean`)
and the read-through in `theory/math/numbersystems/padic_real213.md`: a p-adic integer is a
**branch of the p-ary tree** — an infinite digit stream reached by no finite prefix.  Here
that is made a *theorem* in the same νF carrier as a König binary-tree branch.

For `p = 2` the fit is exact and faithful: a 2-adic digit is a `Bool` (`Fin 2 ≃ Bool`),
so a `ZpSeq 2` *is* a `Nat → Bool` bit-stream, and `CoResidue.boolSpine_escapes` gives:
the 2-adic integer, as a νF inhabitant (`SlashNu`), is **reached by no finite Raw**.  So
`ℤ₂` sits inside the residue's escapes — a 2-adic integer is literally a branch of König's
binary tree, never a finite Raw, never a frozen value.

For **general `p`** the same νF carrier now applies: `CoResidue.gspine` is the label-generic
spine (§20), so a `ZpSeq p` digit stream `Nat → Fin p` rides the **p-ary** spine
`gspine x.digits : GCoShape (Fin p)` — the same binary König branch structure, leaf-labelled by
`Fin p`.  `padic_is_nu_escape` gives: the p-adic integer, as a generic-νF inhabitant, is
reached by no finite Raw, for every `p ≥ 2`.  So **`ℤ_p` for every `p` sits on one carrier** —
the 2-adic case (`twoAdic_is_nu_escape`) is the `Fin 2 ≃ Bool` instance.  ℝ rides the same
carrier via `Real213/NuEscape.lean`.
-/

namespace E213.Lib.Math.NumberSystems.Padic

open E213.Theory.Raw.CoResidue
open E213.Theory (Raw)

/-- A 2-adic integer's digit stream as a `Nat → Bool` bit-stream (`Fin 2 ≃ Bool`,
    faithful: digit `k` ↦ whether it is `1`). -/
def twoAdicBits (x : ZpSeq 2) : Nat → Bool := fun k => (x.digits k).val == 1

/-- ★ **A 2-adic integer IS a residue escape.**  Its bit-stream packages as a νF
    inhabitant (`SlashNu`) — the same carrier as a König binary-tree branch. -/
def twoAdicNu (x : ZpSeq 2) : SlashNu := boolSpineSlashNu (twoAdicBits x)

/-- The 2-adic integer is a genuine slash-νF co-tree: consistent and anti-reflexive. -/
theorem twoAdic_is_nu (x : ZpSeq 2) :
    Consistent (twoAdicNu x).val ∧ AntiRefl (twoAdicNu x).val :=
  (twoAdicNu x).property

/-- ★★ **A 2-adic integer is reached by no finite Raw.**  Its bit-stream escape differs
    (as a labelled co-tree) from every finite Raw's embedding (`rawToSlashNu`), by
    `boolSpine_escapes`.  So `ℤ₂` ⊂ the νF escapes: a 2-adic integer is a branch of
    König's binary tree, never a finite Raw — the same `boolSpine_escapes` shape as
    `KonigConditional.konig_infinity_no_finite_raw`. -/
theorem twoAdic_is_nu_escape (x : ZpSeq 2) (r : Raw) :
    (rawToSlashNu r).val ≠ (twoAdicNu x).val :=
  fun h => boolSpine_escapes (twoAdicBits x) r.val h.symm

/-! ## General `p` — the p-ary spine: `ℤ_p` rides the one νF carrier

The 2-adic escape above rides the binary νF carrier (`Fin 2 ≃ Bool`).  For **general `p`** the
label-generic spine `CoResidue.gspine` (§20) carries it directly: a `ZpSeq p` digit stream
`Nat → Fin p` is `gspine x.digits : GCoShape (Fin p)` — the same binary König branch structure,
leaf-labelled by `Fin p`.  It is a generic-νF inhabitant (consistent + anti-reflexive) and is
reached by no finite Raw (`gspine_escapes`), for every `p ≥ 2`. -/

/-- The two distinct atom labels in `Fin p` (the `gToShape` embedding's `a`/`b`), for `p ≥ 2`. -/
def finA (p : Nat) (hp : 2 ≤ p) : Fin p := ⟨0, Nat.le_of_succ_le hp⟩
def finB (p : Nat) (hp : 2 ≤ p) : Fin p := ⟨1, hp⟩

/-- ★ **A p-adic integer IS a residue escape, for every `p ≥ 2`.**  Its digit stream packages
    as a generic-νF inhabitant (`GSlashNu (Fin p)`) on the p-ary spine — the same carrier as a
    König binary-tree branch, leaf-labelled by `Fin p`. -/
def padicNu {p : Nat} (x : ZpSeq p) : GSlashNu (Fin p) := gspineSlashNu x.digits

/-- The p-adic integer is a genuine generic-νF co-tree: consistent and anti-reflexive. -/
theorem padic_is_nu {p : Nat} (x : ZpSeq p) :
    GConsistent (padicNu x).val ∧ GAntiRefl (padicNu x).val :=
  (padicNu x).property

/-- ★★★ **A p-adic integer is reached by no finite Raw** (`p ≥ 2`).  Its p-ary spine escape
    differs (as a labelled co-tree) from every finite Raw's `gToShape` embedding, by
    `gspine_escapes`.  So `ℤ_p` ⊂ the νF escapes for every `p` — a p-adic integer is a branch
    of the residue's p-ary tree, never a finite Raw — generalising `twoAdic_is_nu_escape` to the
    one νF carrier (binary König spine, `Fin p` leaves). -/
theorem padic_is_nu_escape {p : Nat} (hp : 2 ≤ p) (x : ZpSeq p) (r : Raw) :
    gToShape (finA p hp) (finB p hp) r.val ≠ (padicNu x).val :=
  fun h => gspine_escapes (finA p hp) (finB p hp) x.digits r.val h.symm

/-- ★★ **Distinct p-adic integers give distinct νF escapes.**  A digit-level difference
    (`∃ k, x.digits k ≠ y.digits k`) gives `GDistinct` spines (`gspine_inj`) — the p-ary spine
    embedding `ℤ_p ↪ GSlashNu (Fin p)` is faithful, ∅-axiom (pointwise digit difference). -/
theorem padic_distinct {p : Nat} {x y : ZpSeq p} (h : ∃ k, x.digits k ≠ y.digits k) :
    GDistinct (padicNu x).val (padicNu y).val :=
  gspine_inj h

/-- ★★★ **A p-adic integer carries the digit-shift dynamics.**  Its p-ary spine is the shift →
    νF coalgebra hom of the digit stream: the root branches, the left subtree reads the lowest
    digit `x.digits 0`, and the right subtree is the spine of the *shifted* (drop-lowest-digit =
    divide-by-`p`) digit stream.  So ℤ_p's odometer-shift sits inside the one νF carrier
    (`gspine_shift_coalgebra`), for every `p`. -/
theorem padic_shift_dynamics {p : Nat} (x : ZpSeq p) :
    (padicNu x).val [] = none
    ∧ (∀ q, gCoLeftAt (padicNu x).val [] q = some (x.digits 0))
    ∧ (∀ q, gCoRightAt (padicNu x).val [] q = gspine (fun n => x.digits (n + 1)) q) :=
  gspine_shift_coalgebra x.digits

/-! ### General `p` — the native Cantor diagonal (`ZpSeq p` is not enumerable)

Beyond the reached-by-none escape, the *not-enumerable* fact holds for every `p ≥ 2` natively:
no enumeration `e : ℕ → ZpSeq p` contains the diagonal sequence, by Cantor's own argument on
the residue's p-ary digit tree.  This is the honest form (pointwise digit difference, not a
`Cardinal` theorem) — the p-adic integers are reached by no enumeration. -/

/-- A Nat-level flip to a different small value: `0 ↦ 1`, `_+1 ↦ 0`. -/
def natFlip : Nat → Nat
  | 0     => 1
  | _ + 1 => 0

theorem natFlip_ne (n : Nat) : natFlip n ≠ n :=
  Nat.casesOn n (fun h => Nat.noConfusion h) (fun _ h => Nat.noConfusion h)

theorem natFlip_le_one : ∀ n, natFlip n ≤ 1
  | 0     => Nat.le_refl 1
  | _ + 1 => Nat.zero_le 1

/-- Flip a digit to a provably different digit (needs `p ≥ 2` so two digits exist). -/
def digitFlip (p : Nat) (hp : 2 ≤ p) (d : Fin p) : Fin p :=
  ⟨natFlip d.val, Nat.lt_of_le_of_lt (natFlip_le_one d.val) hp⟩

/-- The flip really differs. -/
theorem digitFlip_ne (p : Nat) (hp : 2 ≤ p) (d : Fin p) : digitFlip p hp d ≠ d :=
  fun heq => natFlip_ne d.val (congrArg (·.val) heq)

/-- The Cantor diagonal of an enumeration: digit `k` disagrees with the `k`-th entry. -/
def zpDiagonal (p : Nat) (hp : 2 ≤ p) (e : Nat → ZpSeq p) : ZpSeq p :=
  ⟨fun k => digitFlip p hp ((e k).digits k)⟩

/-- ★★ **`ZpSeq p` is reached by no enumeration** (`p ≥ 2`).  For any `e : ℕ → ZpSeq p`,
    the diagonal differs from every `e k` at digit `k` — Cantor on the residue's p-ary
    digit tree, the general-`p` reached-by-none (honest: pointwise difference, no
    `Cardinal`). -/
theorem zpSeq_not_enumerable (p : Nat) (hp : 2 ≤ p) (e : Nat → ZpSeq p) :
    ∃ x : ZpSeq p, ∀ k, x.digits k ≠ (e k).digits k :=
  ⟨zpDiagonal p hp e, fun k => digitFlip_ne p hp ((e k).digits k)⟩

end E213.Lib.Math.NumberSystems.Padic
