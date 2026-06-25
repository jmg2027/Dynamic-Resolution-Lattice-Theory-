# Cross-domain: the carrier-readout weld as a transport functor (main ↔ branch)

Branch built: `Nat213` (Raw-generated ℕ₊) number theory — order, divisibility, gcd, coprimality,
well-ordering, exponentiation, valuation, congruence/CRT — plus the **carrier-readout weld**
(`ToNatReadout.toNat_faithful`; value-level `vp_eq_vpSub`, `isGcd_toNat_eq`, `modeq_toNat_iff`).
Main holds: the rich *native-`Nat`* corpus — `Lib/.../ModArith` (Fermat/Euler/Wilson/CRT, 60+ files),
`multiplicative_divisor_theory`, the count-Lens essays, `vp_separation`, §6.9's `0/∞`-as-pre-Lens-residue.

Insights, jotted as they came up during the merge-prep marathon:

1. **Transport, not re-derivation.** The welds are a *functor* `Nat213 → Nat` carrying the generated
   discipline onto the native one. So main's native results (Fermat `a^p ≡ a`, Euler `a^φ ≡ 1`,
   Wilson) need not be **re-derived** over `Nat213` — they can be **transported** along the readout:
   a native congruence theorem + `modeq_toNat_iff` (reverse) gives the `Nat213` statement. This flips
   the "regrounding" workload: build the *carrier weld* once per operation, then inherit the corpus.
   Concrete probe: state `a^p ≡ a (mod p)` over `Nat213` and prove it by `modeq_toNat_iff.mpr` from a
   native Fermat in additive-congruence form. (The friction is converting native `a%m`-form results
   to the subtraction-free additive form `modeq_toNat_iff` speaks — a one-time bridge lemma.)

2. **The no-zero readout principle is §6.9 cashed out operationally.** Main's §6.9 doctrine —
   `0`/`∞` are one pre-Lens residue, never a stratum-value — is stated at the foundational level.
   The branch's `zero_valued_quantities_are_readouts` (essay) shows *where it bites in computation*:
   valuation, exponent's empty product, and the Bézout/inverse are forced to be readouts into ℕ
   exactly because `Nat213` has no act for `0`. Doctrine (main) + three operational witnesses
   (branch) = one fact at two levels.

3. **The weld is the carrier-level shadow of "two faces of one count".** Main's
   `multiplicativity_is_the_x_count_lens` / `addition_and_multiplication_are_two_faces_of_one_count`
   are function-level (`vp`, the count-Lens reading). `toNat_faithful` is the same functoriality at
   the **carrier** level: the whole order/divisibility/valuation structure is one count read at two
   resolutions (`Nat213` source, `Nat` readout). Captured in essay `two_carriers_one_count`.

**Realized** (transport campaign): `Lens/Number/Nat213/ModArithReadout.lean`. The native-form
converter is `mod_eq_imp_additive` (`A % m = B % m → ∃ k l, A + m·k = B + m·l`, the one-time bridge
from native `%`-form to the additive form `modeq_toNat_iff` speaks; ∅-axiom via the PURE
`div_add_mod_pure`, not Lean-core `Nat.div_add_mod` which is `[propext]`). The transport functor is
`modeq_of_toNat_mod` (`a.toNat % m.toNat = b.toNat % m.toNat → ModEq m a b`). Fermat's little theorem
then transports in one line each: `flt_primary` (`a^p ≡ a (mod p)`, fully `Nat213`-native via
`toNat_pow`) and `flt_main` (`a^(p-1) ≡ 1 (mod p)`, the unit-group form with the exponent read in as
`p.toNat - 1`), both inheriting native `universal_flt_*` — **not** re-derived. The
"build the weld once, inherit the corpus" method (essay #115) demonstrated concretely. ∅-axiom.

**Wilson** is now transported too (`wilson`: `(p-1)! ≡ p-1 (mod p)`, the no-negatives form). This
needed a carrier-side construct — `Peano.factorial` over `Nat213` with readout `toNat_factorial`
(`(n!).toNat = (n.toNat)!`) — so it shows the *general* shape: a transport whose statement names an
operation not yet on the carrier first builds that operation (one clean recursive def + its readout),
then inherits the native proof. Three headlines now ride one functor (`modeq_of_toNat_mod`):
power-based (Fermat ×2) and factorial-based (Wilson).

**Euler's criterion and CRT reconstruction are now transported too** — and they sharpened the method:
the native results are *not* all `%`-form. Euler is **divisibility-first** (`p ∣ aᵐ−1 ∨ p ∣ aᵐ+1`) and
CRT existence is **gcd-first** (`gcd m n = 1`). So the transport functor generalises from one weld to
a small fixed set, one per *reading form*:

* `modeq_of_toNat_mod` — `%`-congruence of readouts → `ModEq` (Fermat, Wilson, CRT residues);
* `modeq_of_dvd_sub` / `modeq_self_of_dvd` — divisibility of a difference / of the value → `ModEq`
  (Euler's `±1`, the `−1` branch as `aᵐ+1 ≡ p ≡ 0`);
* `gcd213_eq_one_of_coprime` — `Nat213` `Coprime` → native `gcd213 = 1` (CRT's hypothesis).

Results: `euler_criterion` (`aᵐ ≡ 1 ∨ aᵐ+1 ≡ 0`), `euler_qr` (QR branch), `crt_reconstruction`
(simultaneous-congruence *existence* via lifting the native Bezout `crtSolve` through `toNat_surj` —
the existence complement to `Congruence.crt_iff`). All ∅-axiom. Euler's criterion did **not** need a
carrier Legendre/`QPart` readout after all — the divisibility-form native statement transports
directly. The lesson: pick the weld by the native theorem's *reading form*, not by re-deriving the
statement on the carrier.

**The multiplicative-order corpus is now transported** (`MulOrderReadout.lean`) — the structure
theory of the unit group `(ℤ/p)*`. The transport upgraded the functor to its **iff** form
`modeq_toNat_mod_iff` (`ModEq m a b ⟺ a.toNat % m.toNat = b.toNat % m.toNat`, both directions): the
order corpus needs *both* legs — the defining congruence `a^ord ≡ 1` lifts OUT (`pow_mulOrd_one`),
while `aᵏ ≡ 1 ⟹ ord ∣ k` consumes a congruence lifted IN (`mulOrd_dvd`). The order itself is a count
read OUT into ℕ (`mulOrd a p := ordModP a.toNat p.toNat`, the valuation/no-zero pattern). Results:
`mulOrd_pos`, `pow_mulOrd_one`, `mulOrd_min` (minimality), `mulOrd_dvd`, `mulOrd_dvd_pred` (Lagrange).
All ∅-axiom.

**The whole quadratic-residue programme is now transported** — primitive roots, the carrier Legendre
symbol, quadratic reciprocity, and the discrete log (`PrimitiveRootReadout`, `LegendreReadout`,
`DiscreteLogReadout`). Two findings:

1. **A carrier Legendre symbol *was* needed — and it is a clean congruence.** `QR p a := ∃ z : Nat213,
   z² ≡ a (mod p)` (bound-free, subtraction-free), reconciled with the native bounded existential
   `∃ z, 1≤z<p ∧ z²%p = a%p` by a single weld `QR_iff_native` (the unit hypothesis `¬ p ∣ a` is what
   keeps the reduced witness off the `0` the carrier forbids — the no-zero gap once more). Through it:
   `legendre_mul_t` (multiplicativity), `quadratic_reciprocity_t` (the law), the two supplements,
   and `qr_iff_even_dlog` (the character is the discrete-log parity — squares = even orbit positions).

2. **Composing-iffs, not rewriting-iffs.** Transporting an `Iff`-valued theorem must build the result
   with `Iff.trans`/`.mp`/`.mpr`; `rw [an_iff]` rewrites a `Prop` and pulls `propext` (caught by the
   axiom scan). All `rw` stayed on `Nat` subterms inside the propositions. This is the iff-form
   analogue of the earlier "pick the weld by reading form" lesson.

Primitive roots needed only the order readout already built (`mulOrd`, `maxOrd213 := maxOrd ·`) plus a
`toNat_surj` lift of the native generator — no new construct.

**The permutation faces and the binomial core are now transported too** (`ZolotarevReadout`,
`BinomialReadout`):

* **Zolotarev** — the Legendre symbol is the **sign** of the multiply-by-`a` permutation, and its
  permutation-matrix **determinant**: `psign213 a p = 1 ⟺ QR p a` (`zolotarev`), `det213 a p = 1 ⟺
  QR p a` (`zolotarev_det`). With `LegendreReadout.QR` and `DiscreteLogReadout.qr_iff_even_dlog`, the
  quadratic character now has **four provably-agreeing readings** on the carrier: square /
  orbit-parity / inversion-sign / determinant. The sign/det are counts read OUT into `Int` (`{±1}`).
* **Binomial core** — `freshman_dream` (`(a+1)^p ≡ a^p+1 mod p`) and `middle_binomial_dvd`
  (`p ∣ C(p,k+1)`), the engine behind `flt_primary`. The dream is `%`-form (existing weld); the
  vanishing is divisibility of the readout count `choose p k`.

**Higher reciprocity has no native source in the repo** — quadratic reciprocity (+ both supplements)
is the ceiling present; there is no cubic/Eisenstein/biquadratic reciprocity theorem to transport.
Lucas' theorem likewise exists only as the `lucasStep` predicate with per-prime smokes (no general
digit-product theorem), so only its binomial precursors transport. Recorded honestly rather than
fabricated.

## General Lucas theorem — already in the corpus (+ recursive form added)

Opening Lucas turned up that **most of it was already proved** (two stale "remainder" claims in
`ModArith/LucasTheorem.lean`, now corrected):

1. **Vandermonde's identity** exists — in fact twice: `DyadicFSM/FLT/Vandermonde.lean` (`vandermonde`)
   and `Combinatorics/Vandermonde.lean` (`vandermonde`, `vandermonde_sum`).  ∅-axiom.
2. **The general Lucas digit-step is proved** — `Combinatorics/LucasStepGeneral.lean`, `lucas_step`:
   `choose (p·n+r) (p·k+s) ≡ choose n k · choose r s (mod p)` for `Prime213 p`, `r,s < p`.  Its
   ingredients are all there: `gen_freshman` (`p ∤ i → choose (p·n) i ≡ 0`, the carry collapse — the
   "two-interior-index extraction" worry was solved there via `sumTo_reflect` + `sumTo_split_at`),
   `choose_pn_pk` (high-digit `choose (p·n) (p·k) ≡ choose n k`), `conv_collapse_lt/ge`.

   *(My session-local `prime_dvd_choose_mul` / `lucas_low` duplicated `gen_freshman` /
   `lucas_prefix_zero`; reverted to avoid duplication.)*

**Deposited** (`LucasStepGeneral.lean`, ∅-axiom): `lucas_div` — the **arbitrary-`m,n` recursive form**
`choose m n ≡ choose (m/p) (n/p) · choose (m%p) (n%p) (mod p)` (the digit-step on the base-`p`
decomposition `m = p·(m/p)+m%p`).  This is general Lucas in usable recursive form: no pre-split into
digits required; iterating it down the quotients determines `choose m n mod p` from the digits.

**The explicit digit-product is now proved** — `Combinatorics/LucasDigitProduct.lean`, `lucas_digits`:
for `n < p^L`, `choose m n ≡ ∏_{i<L} choose ((m/p^i) % p) ((n/p^i) % p) (mod p)` (∅-axiom).  Bounded
iteration of `lucas_div` over the quotient tower (reusing `FactorialLcmProduct.prodTo` + three generic
helpers `prodTo_{congr,split_first,mod}`; digit descent via the pure nested floor `div_div_pure`).
**Lucas' theorem is complete in the corpus** in all three forms: digit-step (`lucas_step`), recursive
(`lucas_div`), explicit digit-product (`lucas_digits`).

## Cubic / Eisenstein reciprocity — started (cubic-residue foundation)

The rational **cubic-residue character** is now in the corpus — `ModArith/CubicResidue.lean`, the cubic
analogue of `DiscreteLogParity` (which read the quadratic character as the discrete-log *parity*):

* `cube_pow_iff_three_dvd_exp` — for a prime `p ≡ 1 mod 3` (`3m = p−1`) and primitive root `g`,
  `g^k` is a cube mod `p` ⟺ `3 ∣ k`;
* `cube_iff_three_dvd_dlog` — per unit `a`: the cubic character is the mod-3 class of its discrete log.

∅-axiom; proof mirrors `qr_pow_iff_even_exp` (cube-root ⟹ `a^m ≡ 1` by Fermat ⟹ `3m ∣ km` ⟹ `3 ∣ k`;
converse exhibits `g^{k/3}`).  `three_mul_dvd_iff` is the cubic `two_mul_dvd_iff`.

**Rung 1 done — the character's value group `μ₃`.** `CayleyDickson/Integer/CubeRootsOfUnity.lean`,
`cube_root_unity` (∅-axiom): `x³ = 1 ⟺ x ∈ {1, ω, ω²}` in `ℤ[ω]` — the codomain of `(·/π)₃`.  Purity
craft: `ℤ[ω]`'s `BEq`-membership (`units6.contains x = true`, defeq to a `||`-chain) extracted via
`orB_elim` + `of_decide_eq_true` per branch, avoiding the `propext`-tainted `List.contains_iff_mem` /
`List.mem_cons` simp lemmas.  Plus `omega_primitive` / `omega2_facts` (the `μ₃` group law).

Runway to the full **cubic (Eisenstein) reciprocity** law: the Eisenstein-integer machinery exists
(`CayleyDickson/Integer/Eisenstein{Euclidean,Gcd,Dvd,Split,…}` — `ℤ[ω]` as a Euclidean domain), and
`ModArith/EisensteinCubeRoot` supplies the primitive cube root of unity mod `p`.  **Rung 2a done — congruence in `ℤ[ω]`.** `CayleyDickson/Integer/EisensteinCongruence.lean`,
`ModEq π α β := π ∣ (α − β)` is an equivalence relation compatible with `+`/`·` (`modEq_congruence`,
∅-axiom) — the residue classes mod `π` form the ring `ℤ[ω]/(π)`, where the cubic character lives.
Built on the `Meta.Algebra213.Ring213` ring laws + the Euclidean-`gcd` `zdvd_add`/`zdvd_zero`.

**Rung 2b (core) done — `ℤ[ω]/(π)` is generated by `ℤ`.** `CayleyDickson/Integer/EisensteinResidue.lean`,
`reduce_to_int` (∅-axiom): if `ω ≡ r (mod π)` then every `α ≡ ↑(α.re + α.im·r) (mod π)` — so the
residue ring is a quotient of `ℤ/p`, the structural heart of `ℤ[ω]/(π) ≅ 𝔽_p`.  Via the `ℤ[ω] = ℤ ⊕
ℤω` decomposition (`decomp`) + `EisensteinCongruence.mul_left` + the `ofInt` ring-hom (`ofInt_add`,
`ofInt_mul`).  (`mul_left` added to `EisensteinCongruence`.)

**Rung 2c done — the residue prime exists unconditionally.**
`CayleyDickson/Integer/EisensteinResiduePrime.lean`, `exists_residue_prime` (∅-axiom): for a prime
`p ≡ 1 (mod 3)`, there is a norm-`p` Eisenstein prime `d` and a rational integer `x` with `ω ≡ x
(mod d)`, so **every** `α ≡ ↑(α.re + α.im·x) (mod d)`.  Cube root `x` from
`EisensteinConverse.cube_root_exists` (`p ∣ x²+x+1`); the norm-`p` prime `d ∣ (x−ω)` from the
refactored `EisensteinSplit.split_dvd` (which now exposes the gcd's divisibility of `x−ω`, with
`split_norm` derived from it); read as `ω ≡ x` by `EisensteinResidue.omega_cong_of_dvd` and propagated
by `reduce_to_int`.  So `ℤ[ω]/(d)` is generated by `ℤ` — a quotient of `ℤ/p`.

Rung 2 is complete: the residue ring `ℤ[ω]/(d)` is (a quotient of) `𝔽_p`.

**Rung 3a done — the rational weld `ℤ/p → ℤ[ω]/(d)`.**  `EisensteinResidue.lean` (the `## The rational
weld` section): `modEq_ofInt_of_dvd` (∅-axiom) — if `‖d‖²` divides `a − b` in `ℤ` then `↑a ≡ ↑b (mod
d)`; with `‖d‖² = p` this is the ring map `ℤ/p → ℤ[ω]/(d)`.  Via `dvd_ofInt_norm` (`d ∣ ↑‖d‖²`, from
`d·conj d = ↑‖d‖²`) + `ofInt_dvd`/`ofInt_neg`/`zdvd_trans`.  Both directions of the residue
correspondence are now welds: `reduce_to_int` (`ℤ[ω] → ℤ` mod `d`, rung 2b) and `modEq_ofInt_of_dvd`
(`ℤ/p ↪ ℤ[ω]/(d)`).

**Rung 3b done — the character cubes to one.**  `CayleyDickson/Integer/EisensteinCubicChar.lean`
(`pow_cong`, `ofInt_pow`, `ofInt_pow_modeq_one`, `pow_add`, `half_pow_cube_one`, `char_cubes_to_one`,
all ∅-axiom).  Reusing `RootOfUnityOrthogonality.pow`/`one`, the residue Fermat lift
`ofInt_pow_modeq_one` (`‖d‖² ∣ aⁿ − 1 ⟹ (↑a)ⁿ ≡ 1 mod d`, via `ofInt_pow` + `modEq_ofInt_of_dvd`) and
power additivity `pow_add` give the capstone `char_cubes_to_one`: for **any** `α ∈ ℤ[ω]`, the
half-power `χ(α) := α^m` (`m = (p−1)/3`, `3m = m+m+m`) satisfies `χ(α)³ ≡ 1 (mod d)` — the character
value is a cube root of unity in the residue field `ℤ[ω]/(d) ≅ 𝔽_p`.  Chain: `α ≡ ↑r` (reduction,
rung 2b) → `α^{3m} ≡ (↑r)^{3m}` (`pow_cong`) → `(↑r)^{3m} ≡ ↑1` (`ofInt_pow_modeq_one`, rational
Fermat `r^{p−1} ≡ 1 mod p`).

Next rungs:
**(3c)** read the cube-root-of-unity value into `μ₃` *exactly* (it is one of `{1, ω, ω²}`, not merely
cubing to 1) — needs the residue field's root-counting (`x³ = 1` has exactly 3 roots in `𝔽_p`,
`p ≡ 1 mod 3`), then weld the character `(α/d)₃` to `ModArith/CubicResidue.cube_iff_three_dvd_dlog`;
**(3d)** character multiplicativity `(αβ/d)₃ = (α/d)₃·(β/d)₃` + the weld to the rational cubic
character (norm-`p` primes ↔ `ModArith/CubicResidue.cube_iff_three_dvd_dlog`);
**(4)** primary primes (the unique associate `≡ 2 mod 3` among the 6 unit multiples);
**(5)** the reciprocity `(π/π')₃ = (π'/π)₃`.
Higher (Eisenstein/quartic) reciprocity sits beyond.  With `the_descent_leg` (leg-2 readout).
</content>
