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

Next transportable headlines along the same weld (all native in `Lib/.../ModArith`, `%`-form):
Wilson (`(p-1)! ≡ -1`), CRT reconstruction, Euler's criterion — each a `modeq_of_toNat_mod` instance
once stated over the readouts. Sits with `the_descent_leg` (leg-2 readout).
</content>
