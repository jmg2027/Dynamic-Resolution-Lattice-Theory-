# CRT is a cross-domain Lens-isomorphism — `L_{mk} ≈ prodLens(L_m, L_k)` for coprime `m,k`

**Reproduced result.** The Chinese Remainder Theorem, for coprime `m, k`, as a **kernel
coincidence between two independently-built readings of the residue**:

> `LensIso (leavesModNat (m·k)) (prodLens (leavesModNat m) (leavesModNat k))`
> (`ModArith.LensCRTGeneral.leavesModNat_crt`, `gcd(m,k) = 1`).

The mod-`mk` reading `L_{mk}` and the `(mod-m, mod-k)` product reading `prodLens(L_m, L_k)`
have the *same kernel on `Raw`* — they partition pointings identically. ∅-axiom
(`lean/E213/Lib/Math/NumberTheory/ModArith/LensCRTGeneral.lean`, 3/3 PURE), generalizing the
corpus's concrete `L_6 ≈ prodLens(L_2, L_3)` (`ModArith.LensCRT`) to all coprime moduli.

## Why it matters — the number-theoretic primacy-witness

The §7.1 primacy claim is that every pointing framework is the *same residue* read through a
Lens, so its sharpest internal test is a **proven kernel coincidence between two independently-
built Lenses**, with a property transported across.
A `LensIso` between two *abstract* `Lens` instances is tautology-prone (the corpus's
`Lens/Instances/` carry genuinely distinct kernels, so a non-trivial equal-kernel pair is not
just sitting there). CRT is the genuine, non-tautological instance: `L_{mk}` is built from the
mod-`mk` fold, `prodLens(L_m, L_k)` from two *separate* folds (mod-`m` and mod-`k`); that they
coincide is the content of CRT, not a definitional accident. So this is the cross-domain
primacy-witness the programme wanted — one residue, two readings, equal kernel, proven.

## Derivation — the two refinements

`LensIso L M := L.refines M ∧ M.refines L`, and `lensIso_iff_kernel_eq` reads it as
`∀ x y, L.equiv x y ↔ M.equiv x y` (same partition). The two directions:

**Meet direction** (`L_{mk} ⊑ prodLens(L_m, L_k)`, `leavesModNat_refines_prod`). `prodLens` is
the lattice meet, so `L_{mk}` refines it iff `L_{mk}` refines both factors — and `m ∣ mk`,
`k ∣ mk` give `L_{mk} ⊑ L_m`, `L_{mk} ⊑ L_k` by `divides_refines` (coarser modulus = coarser
partition). No coprimality needed here.

**CRT direction** (`prodLens(L_m, L_k) ⊑ L_{mk}`, `prod_refines_leavesModNat`). This is where
coprimality enters: two pointings agreeing mod `m` and mod `k` must agree mod `mk`. Reading off
`leaves r % m = leaves r' % m` and `% k`, project both residues down to `< mk` (so they share
mod-`m` and mod-`k` residues, `mod_mod_of_dvd`), and `crt_unique` (`gcd(m,k)=1`, uniqueness of
the residue `< mk`) forces them equal. So the product reading determines the mod-`mk` reading
— the CRT isomorphism's forward content.

The concrete `L_6` case discharged this by enumerating the 36 residue pairs; the general case
replaces the enumeration by `crt_unique` (whose own core is `coprime_mul_dvd`:
`m∣d ∧ k∣d ∧ coprime → mk∣d`).

## Dual function — what the iso buys

Classically `ℤ/mk ≅ ℤ/m × ℤ/k` for coprime `m,k`. Read 213-native, it is a kernel coincidence
of two residue-readings: the transport is built in (`refines` both ways *is* "every
mod-`mk`-fact ⟺ a product-fact"). It anchors the Line-A finding that genuine cross-domain unity
lives in shared-engine / shared-kernel theorems — alongside the incidence-Fubini engine, the
SL₂(ℤ) determinant, and the `e` two-homes — not in forced maps.

Honest scope (`§8`). This proves the iso (equal kernel); the explicit reconstruction algorithm
is `CRTReconstruction.crtSolve` (the round-trip `crt_solve_residues`/`crt_unique`). Both
moduli must be positive and coprime for `L_{mk}` to be the meet; without coprimality the product
reading is strictly *coarser* than `L_{mk}` — it equals `L_{lcm(m,k)}` instead (see the lcm-meet
generalization below, since `lcm(m,k) ≤ mk` with equality iff coprime).

## The general lattice statement — the meet is the lcm-modulus (no coprimality)

CRT is one corner of a cleaner fact: for **all** positive `m, k` (drop coprimality), the product
reading is the mod-`lcm` reading.

> `LensIso (leavesModNat (lcm m k)) (prodLens (leavesModNat m) (leavesModNat k))`
> (`ModArith.LensLcmMeet.leavesModNat_lcm`, all positive `m,k`).

So the `leavesModNat` refinement lattice **mirrors the divisibility lattice**: `refines` = `∣`,
and the lattice meet `prodLens` lands exactly on `lcm`. The CRT case is recovered when
`gcd(m,k) = 1` forces `lcm(m,k) = m·k`. The proof reuses the same two-direction skeleton, with
`crt_unique`'s `coprime_mul_dvd` replaced by the **universal property** `lcm_dvd` (every common
multiple of `m` and `k` is a multiple of `lcm`):

  - **Meet direction** (`leavesModNat_refines_prod_lcm`): `m ∣ lcm` and `k ∣ lcm`
    (`dvd_lcm_left/right`) give `L_{lcm} ⊑ L_m, L_k` by `divides_refines`, so `L_{lcm}` refines the
    meet `prodLens(L_m,L_k)`.
  - **lcm direction** (`prod_refines_leavesModNat_lcm`): two pointings agreeing mod `m` and mod `k`
    have their difference divisible by both, hence by `lcm` (`lcm_dvd`), hence — projected `< lcm`
    — equal (`lcm_unique`). No coprimality.

This is the structurally honest home for the result: CRT is not a special fold so much as the
**coprime corner of the modulus-lattice ≅ divisibility-lattice correspondence**, where the meet
collapses to the product `m·k`. ∅-axiom
(`lean/E213/Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean`, 4/4 PURE).

## Cross-frame connections

  - **`ModArith.LensCRT`** — the concrete `L_6` case this generalizes.
  - **`CRTReconstruction`** — the explicit `crtSolve` + uniqueness (`crt_unique`) powering the
    CRT direction.
  - **`Lens/Unified.lean`** (`LensIso`, `lensIso_iff_kernel_eq`) — the "two structures are one"
    kernel-coincidence criterion; CRT is its genuine cross-domain instance.
  - **`ModArith.LensLcmMeet`** — the general lattice statement (meet = lcm-modulus, all positive
    `m,k`); CRT is its coprime corner.
  - **`the_substance_test.md`** "State of Line A" — this is the number-theoretic
    primacy-witness the marathon was assessing; here closed for all coprime moduli, and (via the
    lcm-meet) for the full modulus-lattice ≅ divisibility-lattice correspondence.

## Constructive accessibility

Point at it. The iso: `LensCRTGeneral.leavesModNat_crt`. The two directions:
`leavesModNat_refines_prod` (meet, via `divides_refines` + `prodLens_is_meet`) and
`prod_refines_leavesModNat` (CRT, via `crt_unique` + `mod_mod_of_dvd`). All ∅-axiom
(`#print axioms` empty), 3 PURE / 0 DIRTY.
