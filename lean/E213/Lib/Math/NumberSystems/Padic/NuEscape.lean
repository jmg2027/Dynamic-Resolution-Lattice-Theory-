import E213.Lib.Math.NumberSystems.Padic.Foundation
import E213.Lib.Math.NumberSystems.Padic.Norm
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
open E213.Theory.Raw.Odometer (pOdo pCarry allTop_pcarry_forever pOdo_allTop_zero)
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

/-! ### General `p` — the arithmetic odometer: ℤ_p's `+1` and `-1` on the one carrier

The p-ary spine carries not only the digit-shift (`padic_shift_dynamics`) but ℤ_p's *arithmetic*
successor — the p-ary odometer (`Theory/Raw/Odometer` §8).  `ZpSeq.neg_one` (all digits `p-1`) is
the all-top stream: its `+1`-carry runs forever (`allTop_pcarry_forever`) and wraps to `0`
(`pOdo_allTop_zero`), i.e. `(-1) + 1 = 0`; and it seeds the canonical p-ary escape, reached by no
finite Raw.  So the one-carrier claim is *algebraic*: ℤ_p's residue-unit `+1` acts on
`gspine`-over-`Fin p`, with `-1` the canonical escape. -/

/-- The p-adic `-1` (`ZpSeq.neg_one`, all digits `p-1`) is the all-top digit stream. -/
theorem negOne_all_top (p : Nat) (hp : 0 < p) :
    ∀ n, ((ZpSeq.neg_one p hp).digits n).val + 1 = p := by
  intro n
  show (p - 1) + 1 = p
  cases p with
  | zero   => exact absurd hp (Nat.not_lt_zero 0)
  | succ k => rfl

/-- ★★★ **In ℤ_p, `(-1) + 1 = 0` is the odometer overflow.**  The p-adic `-1`'s digit stream is
    all-top (`negOne_all_top`), so the residue-unit `+1` (`pOdo`) never resolves and wraps every
    digit to `0` (`pOdo_allTop_zero`): `pOdo (neg_one) = zero` as digit streams — the arithmetic
    overflow with nowhere to land. -/
theorem padic_succ_negOne_eq_zero (p : Nat) (hp : 0 < p) :
    ∀ n, pOdo hp (ZpSeq.neg_one p hp).digits n = (ZpSeq.zero p hp).digits n :=
  fun n => pOdo_allTop_zero hp _ (negOne_all_top p hp) n

/-- ★★★ **The arithmetic one-carrier (capstone).**  ℤ_p's residue unit `+1` lives on the one νF
    carrier:

    1. on the p-adic `-1` (all-top stream) the `+1`-carry runs forever (`allTop_pcarry_forever`)
       — the canonical escape, the `+1` demanding a new rung;
    2. `(-1) + 1 = 0`: it wraps to `zero` (`padic_succ_negOne_eq_zero`);
    3. and `-1` is reached by no finite Raw on the p-ary spine (`padic_is_nu_escape`).

    So the one-carrier claim (`the_one_carrier.md`) is *algebraic*, not only dynamical: ℤ_p's
    successor is the residue unit on `gspine`-over-`Fin p`, the p-adic `-1` its canonical escape.
    ∅-axiom. -/
theorem padic_arithmetic_one_carrier (p : Nat) (hp : 0 < p) (hp2 : 2 ≤ p) :
    (∀ n, pCarry (ZpSeq.neg_one p hp).digits n = true)
    ∧ (∀ n, pOdo hp (ZpSeq.neg_one p hp).digits n = (ZpSeq.zero p hp).digits n)
    ∧ (∀ r : Raw,
        gToShape (finA p hp2) (finB p hp2) r.val ≠ (padicNu (ZpSeq.neg_one p hp)).val) :=
  ⟨allTop_pcarry_forever _ (negOne_all_top p hp),
   padic_succ_negOne_eq_zero p hp,
   fun r => padic_is_nu_escape hp2 (ZpSeq.neg_one p hp) r⟩

/-! ### General `p` — multiplication by the base: the valuation filtration on the carrier

Full p-adic multiplication (`Zp.mul`, digit convolution with carry) already exists in `Arith.lean`;
its **multiplicative skeleton** — the valuation/filtration generated by `× p` — is what the one
carrier sees.  `mulBase` (`× p`) shifts the digits up and inserts a `0`: it lands in the maximal
ideal `pℤ_p` (`mulBase_valAtLeast_one`), shifts the valuation up by exactly one
(`mulBase_valAtLeast_succ`, matching `v_p(p·x) = 1 + v_p(x)`), is injective, and its inverse — the
digit-0 drop (`÷p`) — is exactly the carrier's **shift** (`mulBase_coRight`, via CoResidue §21).
The digit-0 readout is the **residue field 𝔽_p** (`residue`, surjective; `× p` reduces to `0`; the
unit `1` is outside the image, so `p` is not a unit).  So the carrier carries ℤ_p's multiplicative
valuation filtration — the `× p` half of the ring, on `gspine`-over-`Fin p`.  All ∅-axiom; full
`Zp.mul`-by-`p` identification (digit convolution) is the remaining follow-up. -/

/-- Prepend a `0` digit (least-significant): the digit function of `p · x`. -/
def consDigit {p : Nat} (hp : 0 < p) (d : Nat → Fin p) : Nat → Fin p
  | 0     => ⟨0, hp⟩
  | k + 1 => d k

/-- **Multiplication by the base `p`** on ℤ_p: shift the digits up, insert `0` at position `0`
    (the valuation operator — the multiplicative generator the carrier sees). -/
def mulBase {p : Nat} (hp : 0 < p) (x : ZpSeq p) : ZpSeq p := ⟨consDigit hp x.digits⟩

theorem mulBase_digit0 {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    (mulBase hp x).digits 0 = ⟨0, hp⟩ := rfl
theorem mulBase_digit_succ {p : Nat} (hp : 0 < p) (x : ZpSeq p) (k : Nat) :
    (mulBase hp x).digits (k + 1) = x.digits k := rfl

/-- ★★★ **`× p` shifts the valuation up by exactly one.**  `valAtLeast (p·x) (n+1) ↔ valAtLeast x
    n`: the digits of `p·x` below `n+1` are zero iff those of `x` below `n` are — `v_p(p·x) = 1 +
    v_p(x)`, the defining property of multiplication by `p`, connecting to the existing valuation
    (`Norm.Zp.valAtLeast`). -/
theorem mulBase_valAtLeast_succ {p : Nat} (hp : 0 < p) (x : ZpSeq p) (n : Nat) :
    Zp.valAtLeast (mulBase hp x) (n + 1) ↔ Zp.valAtLeast x n := by
  constructor
  · intro hv k hk
    exact hv (k + 1) (Nat.succ_lt_succ hk)
  · intro hv k hk
    cases k with
    | zero   => rfl
    | succ j => exact hv j (Nat.lt_of_succ_lt_succ hk)

/-- ★★ **`p·x` lies in the maximal ideal `pℤ_p`** (valuation ≥ 1). -/
theorem mulBase_valAtLeast_one {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    Zp.valAtLeast (mulBase hp x) 1 :=
  (mulBase_valAtLeast_succ hp x 0).mpr (Zp.valAtLeast_zero x)

/-- ★★ **`× p` is injective** (pointwise): `p·x = p·y ⟹ x = y` — `p` is not a zero divisor. -/
theorem mulBase_inj_pointwise {p : Nat} (hp : 0 < p) {x y : ZpSeq p}
    (h : ∀ k, (mulBase hp x).digits k = (mulBase hp y).digits k) :
    ∀ k, x.digits k = y.digits k :=
  fun k => h (k + 1)

/-- The **residue field 𝔽_p** readout: the lowest digit (the reduction `ℤ_p ↠ ℤ_p/pℤ_p = 𝔽_p`). -/
def residue {p : Nat} (x : ZpSeq p) : Fin p := x.digits 0

/-- `p·x` reduces to `0` in 𝔽_p (everything in `pℤ_p` is `0` mod `p`). -/
theorem residue_mulBase {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    residue (mulBase hp x) = (⟨0, hp⟩ : Fin p) := rfl

/-- The residue reduction is **surjective** onto 𝔽_p (the constant stream realises each digit). -/
theorem residue_surjective {p : Nat} (d : Fin p) : ∃ x : ZpSeq p, residue x = d :=
  ⟨⟨fun _ => d⟩, rfl⟩

/-- ★★ **`p` is not a unit: `1 ∉ pℤ_p`.**  The unit `1` reduces to `1 ≠ 0` in 𝔽_p, so it is not in
    the image of `× p` — the maximal ideal is proper. -/
theorem mulBase_ne_one {p : Nat} (hp : 0 < p) (hp1 : 1 < p) (x : ZpSeq p) :
    residue (mulBase hp x) ≠ residue (ZpSeq.one p hp1) :=
  fun heq => Nat.noConfusion (congrArg Fin.val heq : (0 : Nat) = 1)

/-- ★★★ **`÷p` (the carrier's shift) undoes `× p`.**  The right-descent of the spine of `p·x` is
    the spine of `x` (`gspine_coRight` + `mulBase_digit_succ`): on the one carrier, the valuation
    drop is exactly the Bernoulli shift (CoResidue §21).  Its left-descent reads the inserted `0`
    leaf (`mulBase_coLeft`). -/
theorem mulBase_coRight {p : Nat} (hp : 0 < p) (x : ZpSeq p) (q : List Bool) :
    gCoRightAt (gspine (mulBase hp x).digits) [] q = gspine x.digits q :=
  (gspine_coRight (mulBase hp x).digits q).trans
    (gspine_congr (fun n => mulBase_digit_succ hp x n) q)

theorem mulBase_coLeft {p : Nat} (hp : 0 < p) (x : ZpSeq p) (q : List Bool) :
    gCoLeftAt (gspine (mulBase hp x).digits) [] q = some (⟨0, hp⟩ : Fin p) :=
  gspine_coLeft (mulBase hp x).digits q

/-- ★★★ **The valuation filtration on the one carrier (capstone).**  ℤ_p's `× p` (the
    multiplicative valuation generator) on `gspine`-over-`Fin p`:

    1. `p·x ∈ pℤ_p` (`mulBase_valAtLeast_one`) and `v_p(p·x) = 1 + v_p(x)`
       (`mulBase_valAtLeast_succ`);
    2. `× p` is injective (`mulBase_inj_pointwise`) — `p` is not a zero divisor;
    3. the residue field 𝔽_p is the lowest-digit readout (`residue`, surjective; `× p` reduces to
       `0`; `1 ∉ pℤ_p`, so `p` is not a unit);
    4. `÷p` (the valuation drop) is the carrier's **shift** (`mulBase_coRight`, CoResidue §21).

    So the carrier carries ℤ_p's multiplicative valuation filtration — the `× p` half of the ring,
    unified with the additive odometer (`padic_arithmetic_one_carrier`) and the shift dynamics on
    one carrier.  Full `Zp.mul`-by-`p` digit-convolution identity is the remaining follow-up.
    ∅-axiom. -/
theorem padic_valuation_one_carrier {p : Nat} (hp : 0 < p) (hp1 : 1 < p) :
    (∀ x : ZpSeq p, Zp.valAtLeast (mulBase hp x) 1)
    ∧ (∀ (x : ZpSeq p) (n : Nat),
        Zp.valAtLeast (mulBase hp x) (n + 1) ↔ Zp.valAtLeast x n)
    ∧ (∀ x y : ZpSeq p,
        (∀ k, (mulBase hp x).digits k = (mulBase hp y).digits k) → ∀ k, x.digits k = y.digits k)
    ∧ (∀ d : Fin p, ∃ x : ZpSeq p, residue x = d)
    ∧ (∀ x : ZpSeq p, residue (mulBase hp x) ≠ residue (ZpSeq.one p hp1))
    ∧ (∀ (x : ZpSeq p) q, gCoRightAt (gspine (mulBase hp x).digits) [] q = gspine x.digits q) :=
  ⟨mulBase_valAtLeast_one hp,
   mulBase_valAtLeast_succ hp,
   fun _ _ h => mulBase_inj_pointwise hp h,
   residue_surjective,
   mulBase_ne_one hp hp1,
   mulBase_coRight hp⟩

/-! ### General `p` — `mulBase` IS multiplication by the element `p` (the full ring identity)

`mulBase` is not merely shaped like `× p`: it **is** the existing ring multiplication `Zp.mul`
(`Arith.lean`) by the p-adic element `p` (digit `1` at position `1`, `p = 1·p¹`).  The key fact:
multiplication by `p` **carries nothing** — each convolution term `(pElem.digits i)·(x.digits …)`
is `0` except `i = 1`, where it is a single digit `< p` — so `mulCarry = 0` throughout and the
product collapses to the digit shift.  This closes the follow-up of `padic_valuation_one_carrier`:
the carrier's valuation generator is the genuine ring `× p`.  ∅-axiom. -/

/-- The p-adic element `p` itself: digit `1` at position `1`, `0` elsewhere (`p = 1·p¹`). -/
def pElem {p : Nat} (hp0 : 0 < p) (hp1 : 1 < p) : ZpSeq p :=
  ⟨fun k => match k with
    | 0     => ⟨0, hp0⟩
    | 1     => ⟨1, hp1⟩
    | _ + 2 => ⟨0, hp0⟩⟩

/-- The convolution `mulRawSum` against `pElem` collapses to the single `i = 1` term: for any
    `upper ≥ 2`, `Σ_{i<upper} (pElem.digits i)·(x.digits (k-i)) = x.digits (k-1)`. -/
theorem mulRawSum_pElem {p : Nat} (hp0 : 0 < p) (hp1 : 1 < p) (x : ZpSeq p) (k : Nat) :
    ∀ m, Zp.mulRawSum p (pElem hp0 hp1) x k (m + 2) = (x.digits (k - 1)).val
  | 0 => by
      show (0 + 0 * (x.digits (k - 0)).val) + 1 * (x.digits (k - 1)).val = (x.digits (k - 1)).val
      rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul]
  | m + 1 => by
      show Zp.mulRawSum p (pElem hp0 hp1) x k (m + 2)
            + 0 * (x.digits (k - (m + 2))).val = (x.digits (k - 1)).val
      rw [mulRawSum_pElem hp0 hp1 x k m, Nat.zero_mul, Nat.add_zero]

/-- `p · x` has raw digit `0` at position `0`. -/
theorem mulRaw_pElem_zero {p : Nat} (hp0 : 0 < p) (hp1 : 1 < p) (x : ZpSeq p) :
    Zp.mulRaw p (pElem hp0 hp1) x 0 = 0 := by
  show (0 : Nat) + 0 * (x.digits 0).val = 0
  rw [Nat.zero_mul, Nat.add_zero]

/-- `p · x` has raw digit `x.digits j` at position `j+1` (the shift). -/
theorem mulRaw_pElem_succ {p : Nat} (hp0 : 0 < p) (hp1 : 1 < p) (x : ZpSeq p) (j : Nat) :
    Zp.mulRaw p (pElem hp0 hp1) x (j + 1) = (x.digits j).val :=
  mulRawSum_pElem hp0 hp1 x (j + 1) j

/-- ★★ **Multiplication by `p` carries nothing.**  `mulCarry (pElem) x = 0` everywhere: each raw
    convolution digit is a single digit `< p`, so the carry never accumulates. -/
theorem mulCarry_pElem {p : Nat} (hp0 : 0 < p) (hp1 : 1 < p) (x : ZpSeq p) :
    ∀ k, Zp.mulCarry p (pElem hp0 hp1) x k = 0
  | 0     => rfl
  | k + 1 => by
      rw [Zp.mulCarry_succ, mulCarry_pElem hp0 hp1 x k, Nat.add_zero]
      cases k with
      | zero   => rw [mulRaw_pElem_zero hp0 hp1 x]; exact Nat.div_eq_of_lt hp0
      | succ j => rw [mulRaw_pElem_succ hp0 hp1 x j]; exact Nat.div_eq_of_lt (x.digits j).isLt

/-- ★★★ **`mulBase` is the genuine ring `× p`.**  `Zp.mul (pElem) x = mulBase x` (pointwise): the
    existing p-adic multiplication by the element `p` equals the valuation/shift operator, because
    multiplication by `p` carries nothing (`mulCarry_pElem`) and its raw digits are the shift
    (`mulRaw_pElem_zero`/`_succ`).  So `padic_valuation_one_carrier`'s `× p` is the actual ring
    multiplication — the multiplicative valuation on the carrier is grounded in `Zp.mul`. -/
theorem mulBase_eq_mul_pElem {p : Nat} (hp0 : 0 < p) (hp1 : 1 < p) (x : ZpSeq p) :
    ∀ k, (Zp.mul p hp0 (pElem hp0 hp1) x).digits k = (mulBase hp0 x).digits k := by
  intro k
  apply Fin.ext
  rw [Zp.mul_digit_val, mulCarry_pElem hp0 hp1 x, Nat.add_zero]
  cases k with
  | zero   =>
      rw [mulRaw_pElem_zero hp0 hp1 x]
      exact Nat.mod_eq_of_lt hp0
  | succ j =>
      rw [mulRaw_pElem_succ hp0 hp1 x j]
      exact Nat.mod_eq_of_lt (x.digits j).isLt

/-! ### General `p` — reconciliation with `Zp.shiftLeft`, and the real-ring additive grounding

Two closures.  (i) **Repo-first**: `mulBase` is the existing `Zp.shiftLeft … 1` (the `×p^k` shift,
`Arith.lean`) — `mulBase_eq_shiftLeft` records this, so the carrier work connects to the existing
filtration theory (`mulBase` is just the cons-presentation, with cleaner defeq for the spine).
(ii) **Additive grounding**: the abstract odometer's overflow (`padic_arithmetic_one_carrier`,
which used the abstract `pOdo`) is the *actual* ring `(-1) + 1 = 0` — `add_negOne_one_zero` proves
`Zp.add (neg_one) (one) = 0` at the digit level (the carry is `1` from position 1 on,
`add_negOne_one_carry`, so every digit `(p-1)+1 ≡ 0`).  So the residue-unit `+1` on the carrier is
the genuine `Zp.add`-by-`one`.  ∅-axiom. -/

/-- ★★ **`mulBase` is `Zp.shiftLeft 1`** (the existing `× p` shift).  Pointwise: position `0` is
    the inserted `0`, position `k+1` is `x.digits k`.  Connects the carrier valuation operator to
    the existing `× p^k` filtration theory (`Arith.lean`). -/
theorem mulBase_eq_shiftLeft {p : Nat} (hp : 0 < p) (x : ZpSeq p) :
    ∀ j, (mulBase hp x).digits j = (Zp.shiftLeft p hp 1 x).digits j := by
  intro j
  apply Fin.ext
  cases j with
  | zero   => exact (Zp.shiftLeft_digit_low p hp 1 x 0 (Nat.lt_succ_self 0)).symm
  | succ k =>
      show (x.digits k).val = ((Zp.shiftLeft p hp 1 x).digits (k + 1)).val
      rw [show k + 1 = 1 + k from Nat.add_comm k 1, Zp.shiftLeft_digit_high p hp 1 x k]

/-- `p / p = 1` (propext-free, via `NatDiv213.mul_div_self_pure`; core `Nat.div_self` is
    axiom-dirty). -/
private theorem p_div_p {p : Nat} (hp1 : 1 < p) : p / p = 1 := by
  have h := E213.Meta.Nat.NatDiv213.mul_div_self_pure 1 p (Nat.lt_of_succ_lt hp1)
  rw [Nat.one_mul] at h; exact h

/-- ★★ **The `(-1) + 1` carry is `1` from position 1 on.**  Adding `1` to `-1` (= all digits
    `p-1`): position 0 overflows (`(p-1)+1 = p`, carry `1`), and each later top digit propagates
    it (`(p-1)+1 = p`, carry `1`). -/
theorem add_negOne_one_carry {p : Nat} (hp1 : 1 < p) :
    ∀ k, Zp.carry p (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp1)) (ZpSeq.one p hp1) (k + 1) = 1
  | 0 => by
      rw [Zp.carry_succ, Zp.carry_zero, Nat.add_zero,
          show ((ZpSeq.one p hp1).digits 0).val = 1 from rfl,
          negOne_all_top p (Nat.lt_of_succ_lt hp1) 0]
      exact p_div_p hp1
  | k + 1 => by
      rw [Zp.carry_succ, add_negOne_one_carry hp1 k,
          show ((ZpSeq.one p hp1).digits (k + 1)).val = 0 from rfl, Nat.add_zero,
          negOne_all_top p (Nat.lt_of_succ_lt hp1) (k + 1)]
      exact p_div_p hp1

/-- ★★★ **`(-1) + 1 = 0` in the actual ring.**  Every digit of `Zp.add (neg_one) (one)` is `0`:
    position 0 is `((p-1)+1) % p = 0`, and each later position is `((p-1) + 0 + 1) % p = 0` (the
    carry is `1`, `add_negOne_one_carry`).  So the abstract odometer overflow
    (`padic_succ_negOne_eq_zero`, via `pOdo`) is the genuine `Zp.add`-by-`one`. -/
theorem add_negOne_one_zero {p : Nat} (hp1 : 1 < p) :
    ∀ k, ((Zp.add p (Nat.lt_of_succ_lt hp1)
            (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp1)) (ZpSeq.one p hp1)).digits k).val = 0 := by
  intro k
  rw [Zp.add_digit_val]
  cases k with
  | zero =>
      rw [Zp.carry_zero, Nat.add_zero,
          show ((ZpSeq.one p hp1).digits 0).val = 1 from rfl,
          negOne_all_top p (Nat.lt_of_succ_lt hp1) 0]
      exact E213.Meta.Nat.AddMod213.mod_self p
  | succ j =>
      rw [add_negOne_one_carry hp1 j,
          show ((ZpSeq.one p hp1).digits (j + 1)).val = 0 from rfl, Nat.add_zero,
          negOne_all_top p (Nat.lt_of_succ_lt hp1) (j + 1)]
      exact E213.Meta.Nat.AddMod213.mod_self p

/-- ★★★ **The additive one-carrier grounding (capstone).**  The residue-unit `+1` on the carrier
    is the genuine ring `Zp.add`-by-`one`:

    1. the abstract odometer overflow `pOdo (neg_one) = zero` (`padic_succ_negOne_eq_zero`);
    2. the *actual* ring `Zp.add (neg_one) (one) = 0` (`add_negOne_one_zero`).

    Both say `(-1) + 1 = 0` on the p-adic carrier — the abstract odometer and the real `Zp.add`
    agree.  Together with `mulBase_eq_mul_pElem` (the `× p` side is the real `Zp.mul`), the
    carrier's unit arithmetic is grounded in the existing ring on both `+` and `×`. -/
theorem padic_additive_one_carrier {p : Nat} (hp1 : 1 < p) :
    (∀ n, pOdo (Nat.lt_of_succ_lt hp1) (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp1)).digits n
            = (ZpSeq.zero p (Nat.lt_of_succ_lt hp1)).digits n)
    ∧ (∀ k, ((Zp.add p (Nat.lt_of_succ_lt hp1)
            (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp1)) (ZpSeq.one p hp1)).digits k).val = 0) :=
  ⟨padic_succ_negOne_eq_zero p (Nat.lt_of_succ_lt hp1), add_negOne_one_zero hp1⟩

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
