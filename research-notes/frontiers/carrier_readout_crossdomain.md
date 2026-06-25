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

Remaining (explicit-form presentation, optional): the closed digit-product `choose m n ≡ ∏ᵢ choose mᵢ
nᵢ` — needs a `prodTo` + base-`p` digit framework (a bounded-iteration induction on `lucas_div`;
watch `div_div` purity).  Genuinely-absent-from-corpus targets: cubic / Eisenstein / higher
reciprocity (no native source).  Sits with `the_descent_leg` (leg-2 readout).
</content>
