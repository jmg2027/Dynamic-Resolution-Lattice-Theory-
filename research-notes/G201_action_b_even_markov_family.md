# G201 — action (b): a new infinite Markov-uniqueness family closed (the even `2·pᵏ` family)

Action (b) was the orbit-realizability c-uniform lift — the genuine open kernel.  `G200` localized the
size route as exhausted; the remaining lever is the realizability/orbit form, uniform in `c`.  Full
Frobenius is open, but one **infinite sub-family** of the uniform lift was reachable and is now closed
`∅`-axiom: the **even `2·pᵏ` family**.

## What was proved (strict ∅-axiom)

`SternBrocotMarkov.markov_two_prime_pow_unique` (`#print axioms … does not depend on any axioms`):

  > for an odd prime `p` (`3 ≤ p`, divisors `1,p`) and `5 ≤ 2·p^(k+1)`,
  > `MarkovMaxUnique (2·p^(k+1))`.

Plus `markovMaxUnique_34` — the **smallest even Markov number** `34 = 2·17`, the first instance.
This extends Button's odd prime-power family (`markov_prime_pow_unique`) to the **even** Markov numbers of
the form `2·pᵏ` (`34 = 2·17`, `194 = 2·97`, …).

## Why this is a genuine new family (and why it's the natural next one)

A Markov number `c ≥ 5` need not be odd (`34, 194, 610` are even).  Uniqueness reduces (`markov_max_unique_tree`)
to `SqrtNegOneTwoRoots c` — that `x² ≡ −1 (mod c)` has at most two roots `±u`.  For **odd** `c` this holds
iff `c` is a prime power (Button, `ω = 1`).  But `2·pᵏ` (`p ≡ 1 mod 4`) *also* has exactly two roots
(mod `2`: one root; mod `pᵏ`: two; CRT: two) — so it is the next family the same tree machinery closes,
once the two-roots input is supplied.

## The number theory: CRT recombination (`MarkovPrimeFactor.two_roots_of_two_prime_pow`, ∅-axiom)

The prime-power two-roots split (`two_roots_pow_ordered`) needs `∀ n, ¬p∣n → gcd(n, m) = 1`, which **fails**
for `m = 2·pᵏ` (the factor `2` is `p`-coprime but not `m`-coprime).  So `2·pᵏ` is not a mere instantiation;
it needs **CRT recombination**:

  - reduce a root mod `2·pᵏ` to a root mod `pᵏ` (`root_mod_P`, via `dvd_sq_sub_mod_sq`) and reuse
    `two_roots_of_prime_pow` ⟹ `x%pᵏ = y%pᵏ` or `x%pᵏ + y%pᵏ = pᵏ`;
  - force oddness mod `2` (`odd_of_two_dvd_sq_succ`): both roots are odd;
  - recombine `2 ∣ a ∧ pᵏ ∣ a ⟹ 2·pᵏ ∣ a` (`two_P_dvd`, via `euclid_of_coprime` and `gcd(2,pᵏ)=1`),
    giving `x = y` (equal residues, equal parity) or `x + y = 2·pᵏ` (`eq_p_of_dvd`).

All `∅`-axiom.  The pure-`ℕ` discipline forced replacing propext-tainted core lemmas (`Nat.div_add_mod`,
`Nat.mod_two_eq_zero_or_one`, `Nat.mul_assoc`, `Nat.add_sub_add_right`, …) with the repo's pure
equivalents (`AddMod213.div_add_mod`, `AddMod213.mod_two_zero_or_one`, `NatHelper.mul_assoc`,
`NatHelper.add_sub_add_right`, `NatHelper.mul_sub`, `NatHelper.mul_mod_right`).

## Honest scope

This is **one infinite family** of the orbit-realizability uniform lift, not full Frobenius.  It is exactly
the `ω = 1`-shaped case carried over to the even side (root count still `2`).  The genuinely open kernel
remains `ω ≥ 2` (≥ 4 roots, the realizability/phantom-elimination question of `G200`'s orbit form):
no new instruction, no size argument — the irreducible number-theoretic realizability, uniform in `c`.

## Status (Markov uniqueness, ∅-axiom families)

| family | status |
|---|---|
| odd prime power `pᵏ` (Button) | closed — `markov_prime_pow_unique` |
| even `2·pᵏ` | **closed (this)** — `markov_two_prime_pow_unique` |
| specific composites `985, 1325` | closed — orbit/decide (`markov_max_unique_{985,1325}_via_orbit`) |
| general `ω ≥ 2` | open = the realizability residue of `H` |

### Pointers (all ∅-axiom)
- `SternBrocotMarkov.{markov_two_prime_pow_unique, markovMaxUnique_34}`
- `MarkovUniqueness.sqrtNegOneTwoRoots_two_prime_pow`
- `MarkovPrimeFactor.two_roots_of_two_prime_pow` (+ helpers `root_mod_P`, `odd_of_two_dvd_sq_succ`,
  `two_P_dvd`, `dvd_sub_of_mod_eq`, `dvd_sq_sub_mod_sq`)
- prior: Button `markov_prime_pow_unique`; orbit form `markov_max_unique_of_orbit`; `G200` (size route exhausted)
