# Every number is four squares: the additive pigeonhole the counting-bound engine cannot reach

Every natural number is a sum of four squares. The fact is one line —
`nat_isSum4 : ∀ n, isSum4 ↑n` (`lean/E213/Lib/Math/NumberTheory/FourSquare.lean`) — but the
*shape* of its proof is what distinguishes it from the disc-`−3`/`−4`/`−D` representation
theorems that sit beside it. Those run on one engine: a multiplicative finiteness fact (a
polynomial over `ℤ/p` has no more roots than its degree) feeding a commutative norm-Euclidean
descent. Four squares breaks that engine on both ends. The seed is an **additive** pigeonhole,
not a root bound; the descent runs over **every** `n`, not one congruence class, and closes
without ever leaving `ℤ`.

## 213-native answer

"Is a sum of four squares" is a single existential predicate on integers —
`isSum4 n := ∃ a b c d : Int, n = a*a + b*b + c*c + d*d` — and it is **closed under
multiplication**: `isSum4_mul` turns `isSum4 m`, `isSum4 n` into `isSum4 (m*n)` by Euler's
four-square identity `four_sq_id`, an eight-variable bilinear ring equation proved by `ring_intZ`
(`lean/E213/Lib/Math/NumberTheory/FourSquare.lean`). Multiplicativity is the whole reason the
problem reduces to primes: factor `n`, represent each prime factor, multiply the representations
back together. The arithmetic content is therefore entirely in two places — *every prime is four
squares*, and *every `n` has a prime factor* — and both are reached constructively.

## Derivation

**The seed is a counting collision, not a root bound.** For an odd prime `p = 2m+1`,
`FourSquareSeed.four_square_seed` produces `x, y ≤ m` with `p ∣ x²+y²+1`. The mechanism is the
repo's first *additive* pigeonhole: the `m+1` residues `{x² mod p}` are pairwise distinct
(`sq_distinct`), and so are the `m+1` residues `{−1−y² mod p}`; together `2m+2 = p+1 > p` values
land in `Fin p`, so two coincide. Distinctness rules out a within-family collision, so the
coincidence is cross-family — `x² ≡ −1−y²`, i.e. `p ∣ x²+y²+1`. The collision itself is
`Combinatorics.Pigeonhole.no_inj_lt` applied to the map `gval`, and the witness is *found*, not
asserted: a bounded 2-D search `findXY` whose `none`-branch is exactly what `no_inj_lt` refutes
(`gval_inj_or_seed`). Two `propext` traps are dodged by construction — decidable divisibility via
`a % p` rather than `Decidable (p ∣ a)`, and the `Int.natAbs` triangle by staying in `ℕ`.

Contrast the disc-`−3`/`−4` seed (`theory/essays/synthesis/representation_theorems_one_counting_bound.md`):
there the input `p ∣ x²+x+1` or `p ∣ x²+1` comes from `RootBound.eval_zero` — a *degree* bound on
roots of `Tᵐ−1`. That bound is multiplicative (it counts fixed points of a power map) and it is
gated by a congruence (`p ≡ 1 mod 3` / `mod 4`) that makes the exponent an integer. The
four-square seed has no exponent and no congruence: it holds for **every** odd prime, because
`p+1 > p` is unconditional. The pigeonhole counts *sums*, the root bound counts *powers* — a
different counting principle.

**The descent stays over `ℤ` and runs on parity.** `descent_core` is the algebraic heart:
given `m·p = Σaᵢ²` and centred residues `aᵢ = qᵢm + Aᵢ` with `m·r = ΣAᵢ²`, Euler's identity
forces `p·r = Σdⱼ²` (each `dⱼ` divisible by `m`, divide through by `m²` using the pure
positive-multiplication cancellation `mul_left_cancel_pos`). The classical Lagrange descent
stumbles on the case `r = m` (the residues all `= ±m/2`), which needs a mod-8 argument. The route
that closes ∅-axiom **splits on the parity of `m`** and never meets that edge:

- `m` **odd** (`= 2k+1`): centred residues satisfy `2|Aᵢ| ≤ m`, and an even quantity `≤` an odd
  `m` is `≤ m−1`, so `4Aᵢ² ≤ (m−1)²` *strictly* (`Asq_bound`, `rlt`). Then `ΣAᵢ² ≤ (m−1)² < m²`
  gives `r < m` with no `r = m` possibility — `odd_descent`.
- `m` **even**: do not descend by residues at all — *halve*. `mp = Σaᵢ²` even forces an even
  count of odd `aᵢ`; pair them into two same-parity pairs and the half-integers
  `((a±b)/2, (c±d)/2)` are integers with `Σ = (m/2)·p` — a ring identity on the halved
  coordinates (`halve4`, `halve_step`). `m → m/2`.

Both branches strictly shrink `m`, so a fuel recursion `descent_rec` drives any `1 ≤ m < p` down
to `m = 1`, i.e. `isSum4 p`. The initial multiple comes from the seed: `seed_multiple` rewrites
`p ∣ x²+y²+1` as `k·p = x²+y²+1²+0²` with `1 ≤ k < p` (because `k·p ≤ 2m²+1 < (2m+1)² = p²`).

**All `n`.** `prime_isSum4` handles `p = 2 = 1²+1²+0²+0²` directly and odd `p` by
seed-then-descent. To reach composites, `nat_isSum4` needs a prime factor of each `n ≥ 2`:
`exists_prime_factor` supplies one by a constructive least-divisor search (`searchDiv` over
`[2,n)`, divisibility decided by `n % k` in `dvd_dec`), the least such divisor being prime because
any smaller proper divisor would have been found first. Then strong recursion on `n` peels one
prime factor at a time and reassembles with `isSum4_mul`; `n = 0` and `n = 1` are the base
witnesses `⟨0,0,0,0⟩`, `⟨1,0,0,0⟩`.

## Dual function

This is Lagrange's theorem with its packaging stripped: no quaternions, no Hurwitz order, no
choice of a maximal order to make division algorithmic. The classical proof reaches for the
non-commutative Hurwitz integers precisely to *have* a norm-Euclidean domain in which `p` factors;
the 213 reading observes that the norm form's multiplicativity is already a ring identity
(`four_sq_id`) and the descent is already an identity on centred/halved integer coordinates — so
the entire apparatus collapses to `ℤ` with `ring_intZ`. The refinement 213 makes sharper: the
"hard case" of the classical descent (`r = m`) is not hard, it is *mis-split*. Cut the recursion
by parity of `m` and the odd branch is strict by an even-`≤`-odd inequality while the even branch
is not a descent at all but a halving — the mod-8 obstruction was an artifact of refusing to look
at `m`'s parity first.

## Cross-frame connections

The repo's representation theorems stand as two engines. The disc-`−3`/`−4`/`−D`
family (`representation_theorems_one_counting_bound.md`, `eisenstein_period_arithmetic.md`) is the
**multiplicative** engine: root-bound seed (`eval_zero`) + commutative norm-Euclidean descent
(`zomega_div_step`, `zi_div_step`, `zsqrt_div_step`), with the field's only fingerprint a covering
radius² `< 1` and the seed gated by a congruence. The four-square theorem is the **additive**
engine: pigeonhole seed (`no_inj_lt` on a sum-collision) + an over-`ℤ` parity descent, ungated by
any congruence and ranging over all `n`. The same negative result that bounds the first engine —
`ZSqrtNegSharp.descent_false_at_three`, where the covering radius crosses `1` at `D = 3` — has no
analogue here, because the four-square descent never asks a lattice to be integrally closed; it
asks integers to have a definite parity. Two finiteness facts (degree bound vs. box-counting
collision), two descents (commutative-CD vs. parity-over-`ℤ`), one closed predicate `isSum4`.

## Open frontier

The four-square statement itself is closed (`nat_isSum4`, ∅-axiom). The adjacent open direction
is on the *other* engine: the disc-`−8` congruence iff (`p ∣ x²+2 ⟹ p = a²+2b²` is closed via
`ZSqrtNegSplit.split_form_two`, but the forward congruence — which primes have `−2` a quadratic
residue — needs the quadratic character of `2`, the `p ≡ 1,3 mod 8` law not yet derived
∅-axiom). The three-square theorem (`n = a²+b²+c²` iff `n ≠ 4ᵏ(8m+7)`) is a separate, genuinely
harder frontier: it has no multiplicative reduction to primes, so neither engine reaches it as
stated.
