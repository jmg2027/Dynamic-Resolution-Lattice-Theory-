import E213.Lens.Number.Nat213.AtomicityCorrespondence
import E213.Lens.Number.Nat213.Bridge
import E213.Lens.Number.Nat213.Chain
import E213.Lens.Number.Nat213.ChainCoreBridge
import E213.Lens.Number.Nat213.ChartGeneral
import E213.Lens.Number.Nat213.Core
import E213.Lens.Number.Nat213.Lenses
import E213.Lens.Number.Nat213.MultSystem
import E213.Lens.Number.Nat213.MultSystemValue
import E213.Lens.Number.Nat213.ChebyshevLower
import E213.Lens.Number.Nat213.NumberingSystem
import E213.Lens.Number.Nat213.Peano
import E213.Lens.Number.Nat213.Divisibility
import E213.Lens.Number.Nat213.Irreducible
import E213.Lens.Number.Nat213.Factorization
import E213.Lens.Number.Nat213.EuclidUnique
import E213.Lens.Number.Nat213.Gcd
import E213.Lens.Number.Nat213.Coprime
import E213.Lens.Number.Nat213.FTA
import E213.Lens.Number.Nat213.Forcing
import E213.Lens.Number.Nat213.Infinitude
import E213.Lens.Number.Nat213.Prime
import E213.Lens.Number.Nat213.Generation
import E213.Lens.Number.Nat213.Raw
import E213.Lens.Number.Nat213.RawCut
import E213.Lens.Number.Nat213.Order
import E213.Lens.Number.Nat213.Tower.NatPairToInt
import E213.Lens.Number.Nat213.Tower.NatPairToQPos
import E213.Lens.Number.Nat213.Tower.NatTripleToZ2
import E213.Lens.Number.Nat213.Tower.PairCompletion
import E213.Lens.Number.Nat213.SignatureMaps

/-! Spec-as-code entry point for `E213.Lens.Number.Nat213`.

  Nat213 — the 213-native positive naturals.  Two equivalent
  representations + their bridge + lens characterizations + Tower:

  ## Sub-modules

    * `Raw`              — Method A Raw chain (canonical Raw-derived;
                           `Raw.fold one one add` closed-codomain
                           catamorphism).  `one := Raw.a`,
                           `succ n := slashOrSelf n Raw.b`.
    * `Peano`            — standalone inductive `Nat213 | one | succ`.
                           Ergonomic Peano representation.
    * `Bridge`           — `toRaw : Peano.Nat213 → Raw` chart
                           embedding; `value_toRaw` bijection;
                           value-level additive / multiplicative
                           homomorphism (`value_toRaw_add`,
                           `value_toRaw_mul`).
    * `Lenses`           — characterization of `Raw → Peano.Nat213`
                           lenses; multiplicity, swap-invariance.
    * `AtomicityCorrespondence`
                         — atomicity 2 + 3 = 5 realised at
                           type-signature level.
    * `NumberingSystem`  — meta pattern over `(Z, C)` choices; Method A
                           as canonical numbering.
    * `RawCut`           — Lean-free cut prototype on
                           `Raw → Raw → Raw`; vertical projection
                           parallel to `Bool213.booleanProj`.
    * `Order`            — native strict order `lt a b := ∃ c, add a c = b`
                           (no Lean `Nat` order, which is propext-dirty);
                           trichotomy, strict square-monotonicity,
                           square-injectivity `a·a = b·b → a = b`, and the
                           native cancellation `mul_left/right_cancel`.
    * `Divisibility`     — the first discipline over `Nat213` (partial order,
                           bottom `one`, no top); cone is `toNat`-free.
    * `Irreducible`      — irreducibility over `Nat213`: `2,3,5` irreducible,
                           `4` not; `lt_succ_iff` enumeration + cofactor
                           bound.  Rung 1 of the FTA-generated capstone.
    * `Factorization`    — factorization existence (`exists_factorization`):
                           every `Nat213` is a product of irreducibles.  Native
                           `Acc lt`/`wf_lt`, decidable `lt`/`Dvd` via a
                           constructive bounded search (no `Classical`).  Rung 2.
    * `EuclidUnique`     — Euclid's lemma (`euclid`): an irreducible is prime;
                           `prime_dvd_prod`.  Subtractive gcd with the scaled
                           multiplicative spec (`gcd_exists_mul`) — the Bézout
                           substitute that fits ℕ₊ (no zero).  Rung 3.
    * `Gcd`              — the gcd discipline (`IsGcd`): divisibility is a
                           meet-semilattice — gcd exists (`isGcd_exists`), is
                           unique (`isGcd_unique`, via `dvd_antisymm`), with the
                           multiplicative law `gcd(c·a,c·b)=c·gcd(a,b)`
                           (`isGcd_mul_left`).  Extracted from `gcd_exists_mul`.
    * `Coprime`          — coprimality (`Coprime a b := IsGcd a b one`):
                           Euclid's coprime-division law `coprime_dvd_mul`
                           (`gcd(a,b)=1`, `a∣b·c` ⟹ `a∣c`), descent to divisors,
                           `coprime_self_imp`.  Built on `Gcd.isGcd_mul_left`.
    * `FTA`              — **the Fundamental Theorem of Arithmetic** (`fta`):
                           existence + uniqueness-up-to-permutation, generated
                           over `Nat213`.  Native propext-free `Perm`/`erase`.
                           Descent-leg capstone (M4); a full classical discipline
                           computed on the Raw-generated carrier.
    * `Forcing`          — the FTA carrier tied to the primitive: Peano's `succ`
                           IS the distinguishing under `Bridge.toRaw`
                           (`peano_succ_is_distinguishing`); a distinguishing-blind
                           reading cannot carry the prime/composite distinction
                           (`factorization_forced_by_distinguishing`).  M5; honest
                           "recognition, not genesis" (Nat213 a parallel inductive).
    * `Infinitude`       — **Euclid's theorem** (`infinitude_of_irreducibles`):
                           no finite list of irreducibles is complete.  Generated
                           over `Nat213` from the FTA — a second discipline-defining
                           theorem after the FTA itself.
    * `Prime`            — **irreducible ⟺ prime** (`irreducible_iff_prime`): the
                           UFD-defining coincidence over `Nat213` (Euclid + the
                           cancellation direction).

  ## Tower/

  ℕ-pair / ℕ-triple → further number systems via diagonal
  quotients.  All three towers start from the same syntactic
  container — `Nat × Nat` or `Peano.Nat213 × Peano.Nat213` —
  and branch by quotient relation:

    * `Tower/NatPairToInt`   — ℤ via additive diagonal quotient
                                (over Lean Nat).  `a + d = b + c`.
    * `Tower/NatPairToQPos`  — ℚ₊ via multiplicative quotient
                                (over Peano.Nat213).  `a · d = b · c`.
    * `Tower/NatTripleToZ2`  — ℤ² via 3-axis projection
                                (over Lean Nat; Eisenstein basis).
                                `(a, b, c) ↦ (a - c, b - c)`.
    * `Tower/PairCompletion` — the invert move once: a generic
                                commutative-cancellative-semigroup pair
                                completion, instantiated at `+` (ℤ) and
                                `·` (ℚ₊).  The group identity emerges as
                                the diagonal — unit-free, since `Nat213`
                                has no additive `0`.

  All theorems ∅-axiom.
-/
