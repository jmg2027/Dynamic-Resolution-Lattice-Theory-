# Incidence-algebra inversion — one antipode under the two cuts of ℕ

**Reproduced result.** Three inversion theorems, each long-closed and ∅-axiom:

  - **binomial inversion** — `g(n) = Σ_{k≤n} C(n,k)·f(k) ⟹ f(n) = Σ_{k≤n} (−1)^{n−k}C(n,k)·g(k)`
    (`Combinatorics.BinomialInversion.binomial_inversion`);
  - **Möbius inversion** — `g(n) = Σ_{d∣n} f(n/d) ⟹ f(n) = Σ_{d∣n} μ(d)·g(n/d)`
    (`NumberTheory.MobiusInversion.mobius_inversion`);
  - **Stirling inversion** — `g(n) = Σ_{k≤n} S₂(n,k)·f(k) ⟹ f(n) = Σ_{k≤n} s(n,k)·g(k)`
    (second-kind / signed-first-kind Stirling numbers, `Combinatorics.StirlingOrthogonality`).

The new content is not any one inversion — it is the **proof that they are one antipode**:
each is inversion in the incidence algebra of a locally finite poset (Rota 1964), read
through a different poset of ℕ. `IncidenceInversion.inversion_from_orthogonality` is the
single engine; `incidence_inversion_three_posets` carries the three triangular instances as
one object, `incidence_inversion_two_cuts` the additive/multiplicative pair. All
declarations `#print axioms`-empty (`lean/E213/Lib/Math/IncidenceInversion.lean`, 9/9 PURE).

## Why we picked it — the two cuts, one antipode

ℕ carries two comultiplications
(`research-notes/frontiers/convolution_comultiplication_crossdomain.md`): the **additive
cut** `Δ_+ : n ↦ Σ_{i+j=n} i⊗j` and the **multiplicative cut** `Δ_× : n ↦ Σ_{d·e=n} d⊗e`.
Each cut's convolution has a structure element (a zeta) and an antipode (its convolution
inverse), and *inversion against the structure element is the same incidence-algebra move*
read through whichever cut. The corpus had both inversions, proved by two unrelated
arguments; the cross-domain claim "these are one antipode" was narrated, not carried by a
theorem. A unification earns the word only with a proven map, never a resemblance — so this
essay supplies the shared engine and exhibits each inversion as its instance.

## Derivation — the shared engine and its two instances

**The engine** (`inversion_from_orthogonality`). In the incidence algebra of a locally
finite poset, the zeta matrix `M` is lower-triangular with unit diagonal, and its Möbius
matrix `S` is the antipode satisfying the orthogonality `Σ_{k} S(n,k)·M(k,i) = δ(n,i)`.
Given those, the transform `g = M·f` inverts to `f = S·g`. The proof is one Fubini swap
(`sumZ_swap`) followed by the orthogonality collapse (`sumZ_delta_collapse`) — exactly the
shape both inversions already had, now abstracted to a single ∅-axiom theorem. (The
lower-triangularity is what lets the inner transform range extend uniformly, `sumZ_extend_tri`.)

**Additive cut → binomial** (`binomial_inversion_via_engine`). The poset is `(ℕ, ≤)`; the
zeta is the Pascal matrix `M(n,k) = C(n,k)` (lower-triangular: `C(k,i) = 0` for `i > k`);
the antipode is the signed binomial `S(n,k) = (−1)^{n−k}C(n,k)`; the orthogonality
`Σ_k (−1)^{n−k}C(n,k)·C(k,i) = δ(n,i)` is `binomial_orthogonality`. Binomial inversion is
`inversion_from_orthogonality` with these — no separate argument.

**Multiplicative cut → Möbius** (`mobius_inversion_via_ring`). The poset is `(ℕ, ∣)`; the
zeta is the constant `1`; the antipode is `μ`, with `μ ∗ 1 = ε` (`mu_conv_one`). Here the
incidence inversion is the pure inverse-element computation in the Dirichlet algebra:

  `μ ∗ g = μ ∗ (1 ∗ f) = (μ ∗ 1) ∗ f = ε ∗ f = f`,

i.e. associativity (`dirichlet_assoc`), the antipode law (`mu_conv_one`), and the unit
(`dconv_eps_one`). This is the *same* incidence-algebra inverse as the binomial case, with
the divisibility poset replacing `(ℕ, ≤)` and the Dirichlet convolution replacing the
triangular matrix product.

**Partition lattice → Stirling** (`stirling_inversion_via_engine`, and its dual). The third
classical poset is the partition lattice `Π_n`. Its zeta is the Stirling number of the
second kind `S₂(n,k)` (lower-triangular: `S₂(k,i) = 0` for `i > k`), its antipode the signed
Stirling number of the first kind `s(n,k)`, and the orthogonality `Σ_k s(n,k)·S₂(k,i) =
δ(n,i)` is `stirling_orthogonality`. So Stirling inversion is `inversion_from_orthogonality`
on `Π_n` — the *same* engine as binomial, a third poset; and the pair being two-sided
(`stirling_orthogonality2`), both directions `S₂ → s` and `s → S₂` are instances
(`incidence_inversion_three_posets`).

So the inversions are one antipode: the poset is chosen (linear order, divisibility, or
partition lattice), the antipode is that poset's Möbius function, and inversion is its
defining orthogonality `S ∗ M = δ`.

## Dual function — what the unification buys

Classically this is Rota's incidence-algebra account of Möbius inversion: binomial
inversion is the Möbius function of the chain/Boolean poset, number-theoretic Möbius
inversion is the Möbius function of the divisibility poset. Read 213-native, it is the
antipode of the two cuts of ℕ made into one checkable object — the additive and
multiplicative faces of "split-then-reglue" inverted by the *same* law. It also gives the
`COUNT`/incidence family a second cross-domain bridge alongside COUNT-duality
(`count_duality.md`): there the unification was two marginals of one Fubini; here it is two
posets' antipodes of one inversion law.

Honest scope (`§8` falsifiability discipline). Both inversions were already closed; this
adds no new inversion. It converts the narrated "one antipode, two cuts" into a theorem,
and it routes the additive face through an explicit abstract engine while the multiplicative
face runs the same incidence inverse in the Dirichlet ring. Merging *both* faces through a
single Lean engine over one index convention (the divisor poset re-expressed as a
triangular matrix over `[0,n]`) is the remaining rung — the conceptual unification is
proven; a single shared Lean term for both is the open refinement.

## Cross-frame connections

  - **COUNT-duality** (`count_duality.md`): the other incidence bridge — union bound and
    LYM as two marginals of one Fubini. Together they read the `COUNT`/incidence family as
    one structure: Fubini (double count) and antipode (inversion) on a 0/1 incidence matrix.
  - **Möbius / Dirichlet ring** (`theory/math/numbertheory/multiplicative_divisor_theory.md`):
    the multiplicative cut's identities (`φ = μ∗id`, `σ_k = id^k∗1`, Jordan `J_k`) are all
    the same antipode `μ` against different structure elements — instances of this engine.
  - **Convolution generating functions** (`theory/math/combinatorics/convolution_generating_functions.md`):
    the additive cut's Cauchy convolution; its antipode (the `(−1)`-alternation formal
    inverse) is the binomial side's structural home.
  - **The two cuts** (`research-notes/frontiers/convolution_comultiplication_crossdomain.md`):
    this closes that note's F2 — the antipode as one construction read through `Δ_+`/`Δ_×`.
  - **Derangements** (`Combinatorics.DerangementInversion`): a worked corollary —
    `D(n) = Σ_k (−1)^{n−k}C(n,k)·k!` is the binomial inverse of `n! = Σ_k C(n,k)·D(k)`
    (`derange_eq_binomial_inverse_fact`), so inclusion–exclusion for derangements is the
    Boolean-lattice antipode on `(ℕ,≤)`, a direct instance of the engine, not a separate
    technique.
  - **Falling factorials** (`Combinatorics.StirlingFallingInversion`): the partition-lattice
    counterpart — `(x)_n = Σ_k s(n,k)·x^k` is the Stirling inverse of `x^n = Σ_k S₂(n,k)·(x)_k`
    (`falling_eq_signed_stirling_pow`), the two Stirling expansions as the two faces of the
    antipode on `Π_n`.

## Constructive accessibility

Point at it. The shared engine: `IncidenceInversion.inversion_from_orthogonality` (with
`sumZ_extend_tri`). Chain poset (additive): `binomial_inversion_via_engine` (via
`binomial_orthogonality`). Partition lattice: `stirling_inversion_via_engine` and
`stirling_inversion_via_engine_dual` (via `stirling_orthogonality`/`stirling_orthogonality2`).
Divisibility poset (multiplicative): `mobius_inversion_via_ring` (via `mu_conv_one`,
`dirichlet_assoc`, `dconv_eps_one`; the antipode law `mu_conv_one_all`). Capstones:
`incidence_inversion_three_posets` (the three triangular instances of one engine) and
`incidence_inversion_two_cuts` (the additive/multiplicative pair). All ∅-axiom
(`#print axioms` empty), 9 PURE / 0 DIRTY by `tools/scan_axioms.py`.
