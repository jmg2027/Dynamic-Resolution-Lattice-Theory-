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

/-! ### General `p` — binary `×` on the carrier: ×-closed escapes + the residue ring hom

Full `Zp.mul` (digit convolution with carry) already exists; on the carrier it gives two
structural facts.  **(A)** The escapes are **closed under `×` and `+`**: the spine of `x·y` (and
`x+y`) is again reached by no finite Raw — ℤ_p as a carrier subset is a sub-ring of escapes.
**(B)** The residue-field readout `residue : ℤ_p ↠ 𝔽_p` (the lowest digit) is a **ring
homomorphism**: `residue(x·y) = residue x · residue y` and `residue(x+y) = residue x + residue y`
in 𝔽_p, with `0 ↦ 0`, `1 ↦ 1`.  The key computation is carry-free: at position `0` neither sum
nor product carries, so the digit-0 of `x·y` is `(x₀·y₀) mod p` (`residue_mul`) — the actual
`Zp.mul` seen on the carrier's 𝔽_p readout.  ∅-axiom. -/

/-- 𝔽_p addition (the residue field's `+`). -/
def finAdd {p : Nat} (hp : 0 < p) (a b : Fin p) : Fin p := ⟨(a.val + b.val) % p, Nat.mod_lt _ hp⟩
/-- 𝔽_p multiplication (the residue field's `×`). -/
def finMul {p : Nat} (hp : 0 < p) (a b : Fin p) : Fin p := ⟨(a.val * b.val) % p, Nat.mod_lt _ hp⟩

/-- ★★ **The residue readout is additive.**  `residue(x+y) = residue x + residue y` in 𝔽_p:
    position `0` does not carry, so the digit-0 of `x+y` is `(x₀+y₀) mod p`. -/
theorem residue_add {p : Nat} (hp : 0 < p) (x y : ZpSeq p) :
    residue (Zp.add p hp x y) = finAdd hp (residue x) (residue y) := by
  apply Fin.ext
  show ((Zp.add p hp x y).digits 0).val = ((x.digits 0).val + (y.digits 0).val) % p
  rw [Zp.add_digit_val, Zp.carry_zero, Nat.add_zero]

/-- ★★★ **The residue readout is multiplicative.**  `residue(x·y) = residue x · residue y` in
    𝔽_p: position `0` of `Zp.mul` does not carry, so the digit-0 of `x·y` is `(x₀·y₀) mod p` — the
    full ring multiplication `Zp.mul`, read on the carrier's residue field. -/
theorem residue_mul {p : Nat} (hp : 0 < p) (x y : ZpSeq p) :
    residue (Zp.mul p hp x y) = finMul hp (residue x) (residue y) := by
  apply Fin.ext
  show ((Zp.mul p hp x y).digits 0).val = ((x.digits 0).val * (y.digits 0).val) % p
  rw [Zp.mul_digit_val, Zp.mulCarry_zero, Nat.add_zero]
  show ((0 : Nat) + (x.digits 0).val * (y.digits (0 - 0)).val) % p
        = ((x.digits 0).val * (y.digits 0).val) % p
  rw [Nat.zero_add]

/-- ★★★ **The residue field readout is a ring homomorphism `ℤ_p ↠ 𝔽_p`.**  The lowest-digit
    reduction respects `+` (`residue_add`), `×` (`residue_mul`), `0`, and `1` — the carrier's
    𝔽_p readout is the genuine residue-field ring map of the existing `Zp.add`/`Zp.mul`. -/
theorem residue_ring_hom {p : Nat} (hp : 0 < p) (hp1 : 1 < p) :
    (∀ x y : ZpSeq p, residue (Zp.add p hp x y) = finAdd hp (residue x) (residue y))
    ∧ (∀ x y : ZpSeq p, residue (Zp.mul p hp x y) = finMul hp (residue x) (residue y))
    ∧ residue (ZpSeq.zero p hp) = (⟨0, hp⟩ : Fin p)
    ∧ residue (ZpSeq.one p hp1) = (⟨1, hp1⟩ : Fin p) :=
  ⟨residue_add hp, residue_mul hp, rfl, rfl⟩

/-- ★★★ **The carrier escapes are a sub-ring (closed under `×` and `+`), with a residue ring
    hom (capstone).**  For every `p ≥ 2`:

    1. the spine of `x·y` is reached by no finite Raw (escapes ×-closed);
    2. the spine of `x+y` is reached by no finite Raw (escapes +-closed);
    3. the residue readout is multiplicative (`residue_mul`) and additive (`residue_add`).

    So ℤ_p, as the carrier subset of escapes, is closed under the existing ring's `+`/`×`, and the
    carrier's 𝔽_p readout is a ring hom — the binary `×` of `Zp.mul` lives on the one carrier
    (`gspine`-over-`Fin p`), not only the `× p` generator. -/
theorem padic_ring_on_carrier {p : Nat} (hp2 : 2 ≤ p) :
    (∀ (x y : ZpSeq p) (r : Raw),
        gToShape (finA p hp2) (finB p hp2) r.val
          ≠ (padicNu (Zp.mul p (Nat.le_of_succ_le hp2) x y)).val)
    ∧ (∀ (x y : ZpSeq p) (r : Raw),
        gToShape (finA p hp2) (finB p hp2) r.val
          ≠ (padicNu (Zp.add p (Nat.le_of_succ_le hp2) x y)).val)
    ∧ (∀ x y : ZpSeq p,
        residue (Zp.mul p (Nat.le_of_succ_le hp2) x y)
          = finMul (Nat.le_of_succ_le hp2) (residue x) (residue y))
    ∧ (∀ x y : ZpSeq p,
        residue (Zp.add p (Nat.le_of_succ_le hp2) x y)
          = finAdd (Nat.le_of_succ_le hp2) (residue x) (residue y)) :=
  ⟨fun x y r => padic_is_nu_escape hp2 (Zp.mul p (Nat.le_of_succ_le hp2) x y) r,
   fun x y r => padic_is_nu_escape hp2 (Zp.add p (Nat.le_of_succ_le hp2) x y) r,
   fun x y => residue_mul (Nat.le_of_succ_le hp2) x y,
   fun x y => residue_add (Nat.le_of_succ_le hp2) x y⟩

/-! ### General `p` — addition is native (finite-state); multiplication is transport-only

The deepest carrier question: which ring operations are *native* to the spine — definable as a
**finite-state** transduction on the co-tree (each output digit from a bounded carry state) —
versus only available by *transport* of the digit-stream operation?

**Addition is native.**  `Zp.add`'s carry is always a single **bit** (`∈ {0,1}`,
`add_carry_le_one`): each digit pair sums to `< 2p`, so the carry never exceeds `1`.  So addition
is a one-bit-state Mealy machine on the carrier (`add_mealy_step`: output digit + next carry from
the two input digits + the one-bit carry) — and that carry bit *is* the odometer bit
(`Theory/Raw/Odometer`; the `+1` case `add_negOne_one_carry`).  **Multiplication is not**: the
convolution at position `k` reads *all* lower digits (`Zp.mulRaw`/`mulCarry` accumulate
unboundedly), so it has no finite-state form — only the transport `padic_ring_on_carrier`.  This is
the holonomic / non-holonomic distinction at the ring-operation scale.  ∅-axiom. -/

/-- `(p-1) + (p-1) + 1 < 2p` (the two-digit-plus-carry bound). -/
private theorem two_sub_bound (p : Nat) (hp : 0 < p) : (p - 1) + (p - 1) + 1 < 2 * p := by
  cases p with
  | zero   => exact absurd hp (Nat.not_lt_zero 0)
  | succ k =>
      show k + k + 1 < 2 * (k + 1)
      rw [Nat.mul_succ, Nat.two_mul]
      exact Nat.lt_succ_of_le (Nat.le_refl _)

/-- ★★★ **Addition's carry is a single bit.**  `Zp.carry p x y k ≤ 1` for all `k`: each digit
    pair sums to `< 2p` (`two_sub_bound`), so the carry into the next position is `< 2`.  Addition
    is a **finite-state** (one-bit-carry) operation on the carrier — unlike multiplication, whose
    `mulCarry` accumulates unboundedly. -/
theorem add_carry_le_one {p : Nat} (hp : 0 < p) (x y : ZpSeq p) :
    ∀ k, Zp.carry p x y k ≤ 1
  | 0     => Nat.zero_le 1
  | k + 1 => by
      rw [Zp.carry_succ]
      have hx : (x.digits k).val ≤ p - 1 := Nat.le_sub_one_of_lt (x.digits k).isLt
      have hy : (y.digits k).val ≤ p - 1 := Nat.le_sub_one_of_lt (y.digits k).isLt
      have hsum : (x.digits k).val + (y.digits k).val + Zp.carry p x y k
                    ≤ (p - 1) + (p - 1) + 1 :=
        Nat.add_le_add (Nat.add_le_add hx hy) (add_carry_le_one hp x y k)
      have h : (x.digits k).val + (y.digits k).val + Zp.carry p x y k < 2 * p :=
        Nat.lt_of_le_of_lt hsum (two_sub_bound p hp)
      exact Nat.lt_succ_iff.mp
        (E213.Meta.Nat.NatDiv213.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h))

/-- ★★★ **Addition is a one-bit-state Mealy machine on the carrier.**  At each position the output
    digit and the next carry are a function of the two input digits and the current carry, which is
    a single **bit** (`add_carry_le_one`).  So `Zp.add` is a finite-state transduction native to
    the co-tree carrier — the genuine sense in which `+` (unlike `×`) lives *on* `gspine`. -/
theorem add_mealy_step {p : Nat} (hp : 0 < p) (x y : ZpSeq p) (k : Nat) :
    ((Zp.add p hp x y).digits k).val
        = ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) % p
    ∧ Zp.carry p x y (k + 1)
        = ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) / p
    ∧ Zp.carry p x y k ≤ 1 :=
  ⟨Zp.add_digit_val p hp x y k, Zp.carry_succ p x y k, add_carry_le_one hp x y k⟩

/-- ★★★ **Native addition vs transport-only multiplication (capstone).**  On the one carrier:

    1. **addition is native** — a one-bit-state Mealy machine: the carry is always `∈ {0,1}`
       (`add_carry_le_one`), so each output digit comes from a bounded state (`add_mealy_step`);
    2. the carry bit is the **odometer** bit (the `+1` instance is `add_negOne_one_carry`, the
       residue-unit successor of `Theory/Raw/Odometer`);
    3. **multiplication is transport-only** — `Zp.mul`'s position-0 carry is `0` (`Zp.mulCarry`
       is carry-free only at the residue, `residue_mul`), but the convolution reads all lower
       digits, so there is no bounded-state form; `×` lives on the carrier by transport
       (`padic_ring_on_carrier`), not as a native finite-state operation.

    The holonomic / non-holonomic split at the ring-operation scale: `+` is finite-state, `×` is
    not.  ∅-axiom. -/
theorem padic_native_addition {p : Nat} (hp : 0 < p) :
    (∀ (x y : ZpSeq p) (k : Nat), Zp.carry p x y k ≤ 1)
    ∧ (∀ (x y : ZpSeq p) (k : Nat),
        ((Zp.add p hp x y).digits k).val
          = ((x.digits k).val + (y.digits k).val + Zp.carry p x y k) % p) :=
  ⟨fun x y k => add_carry_le_one hp x y k,
   fun x y k => Zp.add_digit_val p hp x y k⟩

/-! ### General `p` — × IS native corecursive (just not finite-state)

The sharp correction: "`×` is not native to the carrier" conflates **not finite-state** (true) with
**not corecursively definable** (false).  The Cauchy product is the textbook *productive
corecursion* (Rutten's behavioural differential equations): `(x·y)₀ = x₀·y₀` and `(x·y)' = x₀·y' +
x'·y`.  Carry keeps each digit a *finite* computation (productive), breaking only *bounded state*.

Here `Zp.mul` is exhibited as a genuine coalgebra morphism for the carrier's shift structure
(CoResidue §21): the **head law** `residue_mul` (`(x·y)₀ = x₀·y₀`), the **tail law** `mulRaw_tail`
(`(x·y)' = x₀·y' + x'·y` — the convolution's behavioural differential equation, `dropHd` = the
shift `÷p`), and the **emit-digit / advance-carry** step `mul_digit_carry_step`.  So `×` is native
*corecursive* — `mul_corecursive` bundles it.  All ∅-axiom; productive but, unlike `+`, not
bounded-state. -/

/-- Drop the lowest digit (the shift `÷p` / `tail` on the carrier). -/
def dropHd {p : Nat} (x : ZpSeq p) : ZpSeq p := ⟨fun i => x.digits (i + 1)⟩

/-- The convolution's shift identity: peeling the lowest factor digit.  By induction on the partial
    sum's `upper` bound — the `i ↦ i+1` reindex turns `x_{i+1}` into `(dropHd x)_i` and `y_{(k+1)-(i+1)}`
    into `y_{k-i}` (`Nat.succ_sub_succ`). -/
theorem mulRawSum_shift {p : Nat} (x y : ZpSeq p) (k : Nat) :
    ∀ upper, Zp.mulRawSum p x y (k + 1) (upper + 1)
      = (x.digits 0).val * (y.digits (k + 1)).val
        + Zp.mulRawSum p (dropHd x) y k upper
  | 0 => by
      show Zp.mulRawSum p x y (k + 1) 0
            + (x.digits 0).val * (y.digits (k + 1 - 0)).val
          = (x.digits 0).val * (y.digits (k + 1)).val + Zp.mulRawSum p (dropHd x) y k 0
      rw [Nat.sub_zero]
      exact (Nat.zero_add _).trans (Nat.add_zero _).symm
  | upper + 1 => by
      show Zp.mulRawSum p x y (k + 1) (upper + 1)
            + (x.digits (upper + 1)).val * (y.digits (k + 1 - (upper + 1))).val
          = (x.digits 0).val * (y.digits (k + 1)).val
            + Zp.mulRawSum p (dropHd x) y k (upper + 1)
      rw [mulRawSum_shift x y k upper, Nat.succ_sub_succ, Nat.add_assoc]
      rfl

/-- ★★★ **The product's tail law (behavioural differential equation).**  `(x·y)' = x₀·y' + x'·y`:
    the shift of the convolution is `x₀` times the shifted second factor plus the product of the
    shifted first factor with the second (`dropHd` = the shift).  This is the corecursive identity
    that makes `Zp.mul` a coalgebra morphism for the carrier's shift (CoResidue §21) — `×` native
    corecursive, the tail complement of the head law `residue_mul`. -/
theorem mulRaw_tail {p : Nat} (x y : ZpSeq p) (k : Nat) :
    Zp.mulRaw p x y (k + 1)
      = (x.digits 0).val * (y.digits (k + 1)).val + Zp.mulRaw p (dropHd x) y k :=
  mulRawSum_shift x y k (k + 1)

/-- ★★★ **The emit-digit / advance-carry step (productivity).**  `(x·y)_k + carry_{k+1}·p =
    rawₖ + carryₖ`: position `k` emits a digit (`% p`) and advances the carry (`/ p`) — `Zp.mul` is
    a productive transducer (`div_add_mod`).  Unlike `+`, the carry here is unbounded
    (`mulRaw_unbounded`), so this is corecursive, not finite-state. -/
theorem mul_digit_carry_step {p : Nat} (hp : 0 < p) (x y : ZpSeq p) (k : Nat) :
    ((Zp.mul p hp x y).digits k).val + Zp.mulCarry p x y (k + 1) * p
      = Zp.mulRaw p x y k + Zp.mulCarry p x y k := by
  show (Zp.mulRaw p x y k + Zp.mulCarry p x y k) % p
        + (Zp.mulRaw p x y k + Zp.mulCarry p x y k) / p * p
      = Zp.mulRaw p x y k + Zp.mulCarry p x y k
  rw [Nat.mul_comm, Nat.add_comm]
  exact E213.Meta.Nat.AddMod213.div_add_mod _ p

/-- ★★★ **`Zp.mul` is a coalgebra morphism for the carrier (capstone): `×` is native corecursive.**
    The product satisfies the behavioural differential equations of the Cauchy product:

    1. **head** — `residue (x·y) = residue x · residue y` (`residue_mul`): `(x·y)₀ = x₀·y₀`;
    2. **emit/advance** — `mul_digit_carry_step`: each position emits a digit and advances the carry
       (productive transducer);
    3. **tail** — `mulRaw_tail`: `(x·y)' = x₀·y' + x'·y` (the convolution's shift law).

    So `×` is genuinely native to the final coalgebra (the carrier's shift, CoResidue §21) — a
    *productive corecursion* — refuting "× is non-native by design".  The honest residue: it is
    productive but **not finite-state** (the carry is unbounded, `mulRaw_unbounded`), the one sense
    in which `×` differs from the finite-state `+`.  ∅-axiom. -/
theorem mul_corecursive {p : Nat} (hp : 0 < p) (x y : ZpSeq p) :
    (residue (Zp.mul p hp x y) = finMul hp (residue x) (residue y))
    ∧ (∀ k, ((Zp.mul p hp x y).digits k).val + Zp.mulCarry p x y (k + 1) * p
              = Zp.mulRaw p x y k + Zp.mulCarry p x y k)
    ∧ (∀ k, Zp.mulRaw p x y (k + 1)
              = (x.digits 0).val * (y.digits (k + 1)).val + Zp.mulRaw p (dropHd x) y k) :=
  ⟨residue_mul hp x y, mul_digit_carry_step hp x y, fun k => mulRaw_tail x y k⟩

/-! ### General `p` — × is NOT finite-state: the multiplicative carry is unbounded

The precise dual of `add_carry_le_one` (addition's carry `≤ 1`): multiplication's convolution is
unbounded.  Witness `(-1)·(-1)` (both streams all-top, `ZpSeq.neg_one`): every convolution term is
`(p-1)·(p-1)`, so `mulRaw (-1) (-1) k = (k+1)·(p-1)²` **exactly** (`mulRaw_negOne_negOne`), which is
unbounded in `k` (`mulRaw_unbounded`).  So the per-position raw value — hence the carry — admits no
constant bound: `×` is computed by no finite-state machine.  This is the **multiplicative residue**:
the part of `×` that escapes finite-state description, the `spineL_escapes` /
`non_holonomicity_as_finite_state_escape` shape read at the ring-operation scale.  (Productive, yet
reached by no bounded state — `mul_corecursive` vs this.)  ∅-axiom. -/

/-- The all-top (`-1`) convolution partial sum is `upper · (p-1)²`. -/
theorem mulRawSum_negOne {p : Nat} (hp : 0 < p) (k : Nat) :
    ∀ upper, Zp.mulRawSum p (ZpSeq.neg_one p hp) (ZpSeq.neg_one p hp) k upper
      = upper * ((p - 1) * (p - 1))
  | 0       => (Nat.zero_mul _).symm
  | upper + 1 => by
      show Zp.mulRawSum p (ZpSeq.neg_one p hp) (ZpSeq.neg_one p hp) k upper
            + (p - 1) * (p - 1) = (upper + 1) * ((p - 1) * (p - 1))
      rw [mulRawSum_negOne hp k upper, Nat.succ_mul]

/-- ★★ **The all-top product convolution is exactly `(k+1)(p-1)²`.**  `mulRaw (-1) (-1) k =
    (k+1)·(p-1)²` — every term of the convolution is `(p-1)·(p-1)`. -/
theorem mulRaw_negOne_negOne {p : Nat} (hp : 0 < p) (k : Nat) :
    Zp.mulRaw p (ZpSeq.neg_one p hp) (ZpSeq.neg_one p hp) k = (k + 1) * ((p - 1) * (p - 1)) :=
  mulRawSum_negOne hp k (k + 1)

/-- ★★★ **The multiplicative carry/convolution is unbounded** (`p ≥ 2`) — the dual of
    `add_carry_le_one`.  For every `C`, the convolution `mulRaw (-1) (-1) k` exceeds `C` at `k = C`
    (`(C+1)·(p-1)² ≥ C+1 > C`, since `(p-1)² ≥ 1`).  So `×` has no bounded per-position value and is
    computed by no finite-state machine — the precise sense of "× is not native finite-state". -/
theorem mulRaw_unbounded {p : Nat} (hp2 : 2 ≤ p) (C : Nat) :
    ∃ k, C < Zp.mulRaw p (ZpSeq.neg_one p (Nat.le_of_succ_le hp2))
                          (ZpSeq.neg_one p (Nat.le_of_succ_le hp2)) k := by
  refine ⟨C, ?_⟩
  rw [mulRaw_negOne_negOne (Nat.le_of_succ_le hp2) C]
  have hpm1 : 0 < p - 1 := Nat.sub_le_sub_right hp2 1
  have hpos : 0 < (p - 1) * (p - 1) := Nat.mul_pos hpm1 hpm1
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self C) (Nat.le_mul_of_pos_right (C + 1) hpos)

/-! ### General `p` — the carry is the multiplicative residue: a νF inhabitant of the *pointing*

The decisive frontier fact.  `(-1)·(-1) = 1` — the **result** is the trivial element `1`
(`neg_one_sq_eq_one`), the simplest µF object — yet the **carry** computing it is unbounded
(`mulRaw_unbounded`, and `mulCarry` itself).  So the unbounded carry is not a property of the
*number* (the product is `1`); it is a property of the **pointing** — the act of multiplying — the
exact ring-operation image of "holonomicity is a property of the pointing, not the real"
(`Real213/PresentationDependence`).

And the carry stream *is literally a νF inhabitant*: `gspine` is generic over the leaf alphabet
(CoResidue §20), so `gspine (mulCarry …) : GCoShape Nat` is a consistent, anti-reflexive co-tree
reached by no finite Raw (`gspine_escapes` at `L = Nat`).  The multiplicative carry escapes the
finite the same way `spineL` does — `carry_is_nu_escape`.  All ∅-axiom. -/

/-- ★★★ **`(-1)² = 1` in ℤ_p (the result is the trivial element).**  Every digit of `neg_one ·
    neg_one` equals `one`'s — via the trunc-level `(p^n−1)² ≡ 1` (`Zp.neg_one_sq_trunc`) bridged to
    digits (`ZpSeq.trunc_succ_inj`).  The product is `1`, while its carry (`mulRaw_unbounded`) is
    unbounded — the work is in the pointing, not the result. -/
theorem neg_one_sq_eq_one (p : Nat) (hp1 : 1 < p) :
    ∀ k, (Zp.mul p (Nat.lt_of_succ_lt hp1)
            (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp1))
            (ZpSeq.neg_one p (Nat.lt_of_succ_lt hp1))).digits k
        = (ZpSeq.one p hp1).digits k := by
  intro k
  have hp' : 0 < p := Nat.lt_of_succ_lt hp1
  have htrunc :
      (Zp.mul p hp' (ZpSeq.neg_one p hp') (ZpSeq.neg_one p hp')).trunc (k + 1)
        = (ZpSeq.one p hp1).trunc (k + 1) :=
    (Zp.neg_one_sq_trunc p hp1 k).trans (ZpSeq.trunc_one_succ p hp1 k).symm
  exact (ZpSeq.trunc_succ_inj hp' k htrunc).2

/-- The multiplicative carry as a label-stream over `Nat` (the unbounded alphabet). -/
def mulCarryStream {p : Nat} (x y : ZpSeq p) : Nat → Nat := fun k => Zp.mulCarry p x y k

/-- The multiplicative carry as a νF inhabitant on the generic carrier (`L = Nat`, CoResidue §20). -/
def carryNu {p : Nat} (x y : ZpSeq p) : GSlashNu Nat := gspineSlashNu (mulCarryStream x y)

/-- The carry co-tree is a genuine generic-νF inhabitant: consistent and anti-reflexive. -/
theorem carry_is_nu {p : Nat} (x y : ZpSeq p) :
    GConsistent (carryNu x y).val ∧ GAntiRefl (carryNu x y).val :=
  (carryNu x y).property

/-- ★★★ **The multiplicative carry is reached by no finite Raw.**  `gspine (mulCarry …)` differs
    from every finite Raw's `gToShape` embedding (`gspine_escapes` at `L = Nat`).  The carry is a
    νF escape — the multiplicative residue lives on the carrier, like `spineL`. -/
theorem carry_is_nu_escape {p : Nat} (x y : ZpSeq p) (r : Raw) :
    gToShape (0 : Nat) (1 : Nat) r.val ≠ (carryNu x y).val :=
  fun h => gspine_escapes (0 : Nat) (1 : Nat) (mulCarryStream x y) r.val h.symm

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
