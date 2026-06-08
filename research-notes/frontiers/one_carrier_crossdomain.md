# Cross-domain — the one-carrier branch ↔ merged main

Two insights that surfaced when the `p-ary-spine-r-carrier` branch (one-carrier program:
νF escapes, the multiplicative residue, finite-state vs not) was merged with main (Zolotarev
sign, the Casoratian/C-finite ladder, the determinant/sign stack).

## 1. "A unit result whose generating process is not finite-state" — at two scales

The branch's headline — **finite-state-ness is a property of the *pointing*, not the *number***
(`the_one_carrier.md`) — is the *same* fact main proved one domain over, on sequences.

- **Ring-operation scale (branch).**  `(-1)² = 1` (`neg_one_sq_eq_one`) — a unit result — yet the
  carry computing it is unbounded and is a νF inhabitant (`mulCarry_unbounded`, `carry_is_nu_escape`);
  addition's carry is one bit (`add_carry_le_one`).  Finite-state is decided by the *operation*
  (`+` yes, `×` no), not the result `1`.
- **C-finite / sequence scale (main).**  A sequence whose Casoratian determinant is the unit `q = −1`
  has **no finite holonomic depth** — `WronskianDepth.cas_neg_unit_no_finite_depth` (= `MaxEntropy`),
  the maximum-entropy ceiling of `DetSpectrumPoles`.  The determinant (the result) is the unit `±1`;
  the *generation* (the recurrence depth) escapes every finite-state machine.

**Shared invariant:** a unit / trivial `±1` *output* whose *pointing* (the carry, resp. the
recurrence) is non-finite-state — `object1_not_surjective` / `escape_by_invariant` read on the
process, not the value (`mul_carry_nu_residue` ↔ `cas_neg_unit_no_finite_depth`).  This is the
sequence-scale mirror the branch's frontier note `multiplicative_carry_residue.md` already names
(`G188_multiplicative_conv_design` is the coefficient-scale third witness).

*Open bridge:* a single ∅-axiom statement with both the p-adic carry and the Casoratian depth as
instances of "unit value, non-finite-state pointing" — would unify the two scales the way
`gspine_one_carrier` unified number- and operation-escapes.

## 2. Multiplication: finite-state ⟺ unit; escape ⟺ the non-unit `p`

Main and the branch read the *two halves of the same multiplication map*:

- **Unit side (main, Zolotarev).**  `× a mod p` for a unit `a` is a finite **permutation**
  `σ_a` (`mulPermMod_mem_perms`), with a sign character (`psign_mulPermMod`, → Legendre `(a/p)`).
  Multiplication by a unit is a finite-state bijection.
- **Non-unit side (branch).**  `× p` is the valuation operator `mulBase` = the genuine `Zp.mul`-by-`p`
  (`mulBase_eq_mul_pElem`) — injective **non-surjective**, the shift into `pℤ_p`, with no finite-state
  form (the binary `×` carry is unbounded).

**Shared invariant:** for multiplication, *unit = finite-state permutation (a sign); non-unit `p` =
the valuation escape (the residue)*.  The unit/non-unit split **is** the finite-state/escape split.
Main reads the unit half as a sign character; the branch reads the non-unit half as the multiplicative
residue.

*Honest scope:* these are cross-domain *readings* (the shared invariant named), not yet single
theorems spanning both domains — `σ_a` is a finite mod-`p` permutation, `mulBase` is on infinite
`ℤ_p`; the bridge is the residue/sign character living on opposite sides of the unit boundary.

## Anchors
- branch: `Padic/NuEscape` (`neg_one_sq_eq_one`, `mulCarry_unbounded`, `carry_is_nu_escape`,
  `mulBase_eq_mul_pElem`, `add_carry_le_one`), `CoResidue` §22 (`escape_by_invariant`),
  `theory/essays/foundations/the_one_carrier.md`, `multiplicative_carry_residue.md`.
- main: `Analysis/Cauchy/WronskianDepth` (`cas_neg_unit_no_finite_depth`), `Algebra/DetSpectrumPoles`,
  `NumberTheory/ModArith/ZolotarevSign` (`mulPermMod`, `psign_mulPermMod`), `Lens/Cardinality/Cantor`.
