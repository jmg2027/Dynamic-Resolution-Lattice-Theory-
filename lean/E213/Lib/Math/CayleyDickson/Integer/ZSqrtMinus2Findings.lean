import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2Tower
import E213.Lib.Math.CayleyDickson.Integer.ZI

/-!
# CayleyDickson.Integer.ZSqrtMinus2Findings — Rust→Lean discovery loop

Ad-hoc 213-discoveries about the ZSqrt[-2] CD tower, formalised
∅-axiom from Rust-probe outputs (`algebra213-tower-probe`,
2026-05-09):

  - **SHIFT RULE (smallest instance)**: ZI units (D=1 L2, 4 units
    = Z_4) are unit-loop-isomorphic to L3T (D=2 L3, 4 units).
    Witnessed by an explicit bijection φ + `decide`-checked
    `φ (a·b) = φa · φb` on every unit-pair product.
    Reveals D ≥ 2 ladders as shifted-by-one copies of D=1.
  - **L6 ZERO-DIVISOR WITNESS**: L6 ZSqrt[-2] (32-dim,
    sedenion-position) has zero divisors:
        `(e_1 + e_10) · (e_4 - e_15) = 0`.
    Notably L6 is NOT a sedenion-analogue (alt-L, alt-R, flex all
    hold on basis units), yet zero divisors exist — novel structure.
  - **META-SEARCH PIPELINE**: `findZD` (pure recursive search) +
    `findZD_sound` (soundness lemma) demonstrate the general
    pattern `algorithm cs = some w → P w`, with the existence
    theorem `L6_has_zero_divisor` recovered mechanically via
    `decide` on the find result.

Consolidated 2026-05-18 from `ShiftRule_ZI_L3.lean` +
`ZSqrtMinus2L6Witnesses.lean` + `ZSqrtMinus2L6Search.lean`.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZSqrt

/-! ## SHIFT RULE — ZI ↔ L3T unit-loop isomorphism -/

def ZIUnits : List ZI := [⟨1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]

def L3TUnits : List L3T :=
  [⟨⟨1, 0⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩,
   ⟨⟨0, 0⟩, ⟨1, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1, 0⟩⟩]

/-- Explicit bijection ZI → L3T (real-slot to real-slot). -/
def φ : ZI → L3T
  | ⟨1, 0⟩    => ⟨⟨1, 0⟩, ⟨0, 0⟩⟩
  | ⟨-1, 0⟩   => ⟨⟨-1, 0⟩, ⟨0, 0⟩⟩
  | ⟨0, 1⟩    => ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
  | ⟨0, -1⟩   => ⟨⟨0, 0⟩, ⟨-1, 0⟩⟩
  | _         => ⟨⟨0, 0⟩, ⟨0, 0⟩⟩  -- catchall (not in unit set)

/-- ★ ∅-axiom shift-rule witness: `φ` preserves multiplication on
    all 16 unit-pair products. -/
theorem shift_iso_L3 :
    ∀ a ∈ ZIUnits, ∀ b ∈ ZIUnits, φ (ZI.mul a b) = φ a * φ b := by decide

/-- Bijectivity check (4 distinct image elements). -/
theorem φ_injective_on_units :
    (ZIUnits.map φ).length = ZIUnits.length ∧
    (ZIUnits.map φ).Nodup := by decide

/-! ## L6 ZSqrt[-2] zero-divisor witness -/

-- Zero builders at each layer
def Z2z : ZSqrt 2 := ⟨0, 0⟩
def L3z : L3T := ⟨Z2z, Z2z⟩
def L4z : L4T := ⟨L3z, L3z⟩
def L5z : L5T := ⟨L4z, L4z⟩
def L6z : L6T := ⟨L5z, L5z⟩

-- Basis units. Position-to-path encoding: 5-bit msb-first selector
-- (re=0, im=1) into nested L6T → ... → ZSqrt 2 → .re (always real-slot).
-- e_1  = pos 2  = 0b00010 = re re re im re
-- e_4  = pos 8  = 0b01000 = re im re re re
-- e_10 = pos 20 = 0b10100 = im re im re re
-- e_15 = pos 30 = 0b11110 = im im im im re

def e1  : L6T := ⟨⟨⟨⟨Z2z, ⟨1,0⟩⟩, L3z⟩, L4z⟩, L5z⟩
def e4  : L6T := ⟨⟨L4z, ⟨⟨⟨1,0⟩, Z2z⟩, L3z⟩⟩, L5z⟩
def e10 : L6T := ⟨L5z, ⟨⟨L3z, ⟨⟨1,0⟩, Z2z⟩⟩, L4z⟩⟩
def e15 : L6T := ⟨L5z, ⟨L4z, ⟨L3z, ⟨Z2z, ⟨1,0⟩⟩⟩⟩⟩

def zd_a : L6T := e1 + e10
def zd_b : L6T := e4 - e15

/-- ★ ∅-axiom witness: L6 ZSqrt[-2] has a zero divisor. -/
theorem L6_zd_witness : zd_a * zd_b = L6z := by decide

/-! ## Meta-search pipeline — `findZD` + soundness -/

def findOneZD (a : L6T) : List L6T → Option L6T
  | [] => none
  | b :: bs =>
    if a ≠ L6z ∧ b ≠ L6z ∧ a * b = L6z then some b
    else findOneZD a bs

def findZD : List L6T → List L6T → Option (L6T × L6T)
  | [], _ => none
  | a :: as, bs =>
    match findOneZD a bs with
    | some b => some (a, b)
    | none => findZD as bs

theorem findOneZD_sound (a : L6T) :
    ∀ (bs : List L6T) b, findOneZD a bs = some b →
      a ≠ L6z ∧ b ≠ L6z ∧ a * b = L6z := by
  intro bs
  induction bs with
  | nil => intro b h; cases h
  | cons head tail ih =>
    intro b h
    simp only [findOneZD] at h
    by_cases hp : a ≠ L6z ∧ head ≠ L6z ∧ a * head = L6z
    · rw [if_pos hp] at h; cases h; exact hp
    · rw [if_neg hp] at h; exact ih b h

theorem findZD_sound :
    ∀ (xs ys : List L6T) p, findZD xs ys = some p →
      p.1 ≠ L6z ∧ p.2 ≠ L6z ∧ p.1 * p.2 = L6z := by
  intro xs
  induction xs with
  | nil => intros ys p h; cases h
  | cons a as ih =>
    intro ys p h
    simp only [findZD] at h
    cases hone : findOneZD a ys with
    | none => rw [hone] at h; exact ih ys p h
    | some b =>
      rw [hone] at h; cases h
      exact findOneZD_sound a ys b hone

def candidates : List L6T := [zd_a, zd_b, e1, e4, e10, e15]

theorem findZD_finds_witness :
    findZD candidates candidates = some (zd_a, zd_b) := by decide

/-- ★ ∅-axiom existence via meta-search pipeline. -/
theorem L6_has_zero_divisor :
    ∃ a b : L6T, a ≠ L6z ∧ b ≠ L6z ∧ a * b = L6z := by
  obtain ⟨h1, h2, h3⟩ :=
    findZD_sound candidates candidates _ findZD_finds_witness
  exact ⟨zd_a, zd_b, h1, h2, h3⟩

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
