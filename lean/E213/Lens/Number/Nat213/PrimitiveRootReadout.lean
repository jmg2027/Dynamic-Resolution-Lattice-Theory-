import E213.Lens.Number.Nat213.MulOrderReadout
import E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot

/-!
# Lens.Number.Nat213.PrimitiveRootReadout — maximal order & primitive roots over `Nat213` (∅-axiom)

The **descent leg**, leg-2 — completing the unit-group structure begun in `MulOrderReadout`.  Where
that file transported the order of a *single* element, this one transports the **group-level** facts:
the maximal order `maxOrd p`, that every element's order divides it, that it equals `p − 1`, and the
existence of a **primitive root** (an element of full order `p − 1` — the generator that makes
`(ℤ/pℤ)*` cyclic).

Like `mulOrd`, the maximal order is a count read OUT into ℕ: `maxOrd213 p := maxOrd p.toNat`.  These
are pure ℕ-level / existence facts about the readouts, so they transport directly — the only carrier
work is lifting the native primitive-root witness `g` to a `Nat213` (via `toNat_surj`).

* `mulOrd_dvd_maxOrd` — every unit's order divides the maximal order;
* `maxOrd_eq_pred` — `maxOrd213 p = p − 1` (the group is cyclic of order `p − 1`);
* `exists_primitive_root` — `∃ g : Nat213, mulOrd g p = p − 1` (a full-order generator exists).

Native source: `Lib/.../ModArith/{MaxOrder, EveryOrdDvdMax, PrimitiveRoot}`.  Transported, not
re-derived.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.PrimitiveRootReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (toNat toNat_ge_one)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_surj)
open E213.Lens.Number.Nat213.MulOrderReadout (mulOrd)
open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP)
open E213.Lib.Math.NumberTheory.ModArith.MaxOrder (maxOrd)
open E213.Lib.Math.NumberTheory.ModArith.EveryOrdDvdMax (every_ord_dvd_maxOrd)

/-- **The maximal multiplicative order** mod `p`, over `Nat213` — the largest order of any unit, a
    count read OUT into ℕ: `maxOrd p.toNat`. -/
abbrev maxOrd213 (p : Nat213) : Nat := maxOrd p.toNat

/-- ★★★ **Every unit's order divides the maximal order** — `mulOrd a p ∣ maxOrd213 p`, for a unit
    `1 ≤ a.toNat ≤ p.toNat − 1`.  (The cyclic-group fact behind `maxOrd = p − 1`: the unit group has
    an element whose order is a common multiple of all the others.)  Native `every_ord_dvd_maxOrd` at
    the readouts (positivity `1 ≤ a.toNat` free — no zero on the carrier).  ∅-axiom. -/
theorem mulOrd_dvd_maxOrd {a p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (ha : a.toNat ≤ p.toNat - 1) :
    mulOrd a p ∣ maxOrd213 p :=
  every_ord_dvd_maxOrd p.toNat hp hpr a.toNat (toNat_ge_one a) ha

/-- ★★★ **The maximal order is `p − 1`** — `maxOrd213 p = p.toNat − 1`.  The unit group `(ℤ/pℤ)*` is
    cyclic of order `p − 1`: some element attains the full group order.  Native
    `PrimitiveRoot.maxOrd_eq_pred` at the readouts.  ∅-axiom. -/
theorem maxOrd_eq_pred {p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) :
    maxOrd213 p = p.toNat - 1 :=
  E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot.maxOrd_eq_pred p.toNat hp hpr

/-- ★★★★ **A primitive root exists over `Nat213`** — `∃ g : Nat213`, `g.toNat ≤ p.toNat − 1` and
    `mulOrd g p = p.toNat − 1`: a unit of *full* order, the generator making `(ℤ/pℤ)*` cyclic.
    Native `PrimitiveRoot.exists_primitive_root` builds the native witness `1 ≤ g ≤ p−1` with
    `ordModP g p = p − 1`; `toNat_surj` lifts it to a carrier element (the readout `mulOrd` is
    `ordModP` of the readout, so the order value is preserved).  ∅-axiom. -/
theorem exists_primitive_root {p : Nat213} (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) :
    ∃ g : Nat213, g.toNat ≤ p.toNat - 1 ∧ mulOrd g p = p.toNat - 1 := by
  obtain ⟨g, hg1, hgp, hge⟩ :=
    E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot.exists_primitive_root p.toNat hp hpr
  obtain ⟨g', hg'⟩ := toNat_surj g hg1
  exact ⟨g', by rw [hg']; exact hgp, by show ordModP g'.toNat p.toNat = p.toNat - 1; rw [hg']; exact hge⟩

end E213.Lens.Number.Nat213.PrimitiveRootReadout
