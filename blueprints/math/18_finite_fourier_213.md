# Finite Fourier Analysis 213 — Blueprint (DFT on ℤ/n)

**Priority**: ★★★ (maximal connectivity per unit effort)

Implements **topic C8** of
`research-notes/frontiers/research_program_year_horizon.md` ("Fourier on
ℤ/n — the finite harmonic layer", recommended first topic of the year).

---

## 1. Why This Field

Classically, Fourier analysis on ℤ/n is stated with ℂ-valued characters
`χ_a(x) = e^{2πiax/n}` — the continuous circle is imported to do bookkeeping
that is finite from start to finish.  Every theorem in this blueprint is a
**finite sum identity**: inversion, Parseval/Plancherel, convolution,
Poisson summation.  No limit, no measure, no ℝ, no ℂ.

The 213-native statement first: the DFT is the **count-Lens pairing of a
ℤ/n-valued function against the additive characters** — read a function
through each character-Lens, and the family of readings is faithful
(inversion) and length-preserving (Parseval).  What ZFC calls "harmonic
analysis on a finite abelian group" is, here, the statement that the n
character-Lenses jointly recover the distinguishing they were applied to,
up to the always-present factor `n` (which we never divide out — see §2.3).

Payoffs (each already has a waiting consumer in the repo):

- **Gauss sums become Fourier coefficients** — `g(χ) = Σ_t χ(t)ζ^t` is the
  DFT of the multiplicative character at frequency 1; the quadratic
  reciprocity already CLOSED via the Eisenstein lattice route
  (`ModArith/QuadraticReciprocity.lean`) gets its second, spectral reading.
- **The `K_p` Laplacian spectrum bridge gets its home** —
  `curvature_spectrum_crossdomain.md` bridge 1: the complete-graph
  Laplacian spectrum `{0, p}` (`DiscreteLichnerowicz.km_meanzero_eigen`)
  IS the additive-character spectrum of ℤ/p.  Phase FE closes it.
- **Physics gets its first harmonic-analysis object** — a finite,
  ∅-axiom DFT with Parseval is the prerequisite shape for any future
  mode-decomposition claim in `Lib/Physics/`.
- **Feeds E1 (Gram forcing)** — the normalised ℚ-valued cup the α_em
  `1/d`-graduation leg needs will consume exactly the
  Parseval/orthogonality kernel built here; the un-normalised ℤ-form is
  this blueprint, the `1/n` normalisation is E1's ℚ-cup (flagged, not
  built here).

## 2. 213-native Emergence

### 2.1 A character is a Lens into μ_n, the finite unit shadow

No continuous circle is imported.  μ_n = the n-th roots of unity is a
**finite unit group**, and the repo already carries it three ways:

1. **Inside ℤ[ω] / ℤ[i]** for `n ∈ {1,2,3,4,6}` — the crystallographic
   orders (`CyclotomicTraceDegree.crystallographic_restriction`: rational
   trace ⟺ `n ∈ {1,2,3,4,6}`; `FiniteOrderSpectrum.finite_order_spectrum`).
   `ω` (order 3), `ζ₆ = 1+ω` (order 6) in `ZOmega`; `i` (order 4) in `ZI`.
2. **Inside ℤ/p itself** for every `n ∣ p−1` — `ω = g^{(p−1)/n} mod p`
   (`CyclicCharacterOrthogonality.omega_order_n`), no ring adjoined.
3. **As the basis of the free group ring `R[C_n]`** — `ζ^k = e_k`, a
   coefficient function `Nat → R` with index read mod n
   (`EisensteinGroupRing`).  This is how `ℤ[ζ_n]` is *avoided*: we never
   quotient by the cyclotomic polynomial; the group ring carries the
   universal μ_n and every identity is a **coefficient equation**.

An additive character of ℤ/n is then the Lens `χ_a : x ↦ ζ^{ax}` — a
reading of the additive count into μ_n.  The "unit circle" of classical
Fourier analysis appears only as its finite shadow; the continuum version
is a `Real213` pointing we do not need (transcendental-as-exterior row:
reached-by-none ≠ outside, and here not even pointed at).

### 2.2 Orthogonality is the geometric telescope — already closed

`Σ_x χ_a(x) = 0` for `a ≢ 0` is proven three times over, all ∅-axiom, all
by the same engine `ω·S + 1 = S + ω^n` / `(ζ−1)·S = ζ^n−1`:
order 2 (`CharacterOrthogonality.quadratic_orthogonality`), orders 3,4,6
(`RootOfUnityOrthogonality.root_orthogonality`, `GaussianOrthogonality`),
general `n ∣ p−1` in ℤ/p (`CyclicCharacterOrthogonality.
cyclic_orthogonality_modp`).  Phase FA consolidates these into ONE generic
telescope (repo rule 7: same-topic evolution goes in one file) instead of
adding a fourth copy.

### 2.3 Multiply-through: no ℚ, no 1/n

Inversion classically reads `f(x) = (1/n)Σ_a f̂(a)ζ^{−ax}`.  The
213-native form keeps the count on the left: `n · f(x) = Σ_a f̂(a)·ζ^{−ax}`.
The factor n is the size of the Lens family, a count — dividing it out is
a normalisation *choice* (a flattening Lens), not the content.  Everything
below is stated over a commutative `Ring213` carrier (ℤ, `ZOmega`, `ZI`,
or `R[C_n]` coefficients) in multiply-through form.  **Flag**: the ℚ-form
(actual `1/n`) is needed only by E1's normalised cup and by any future
`L²`-normalised physics statement; it is deferred there, not smuggled in.

### 2.4 No funext: every identity is a coefficient equation

Function equality needs `funext` (Quot-backed, axiom-dirty).  Following
`EisensteinGroupRing`, the DFT is a coefficient function and every theorem
is pointwise: `dft (dft f) x = n · f ((n − x % n) % n)`, never
`dft ∘ dft = n • reflect`.

### 2.5 Conjugation is index reflection

In the free group ring, `conj χ_a = χ_{n−a}` — conjugation is negation of
the frequency index, a pair-swap (Bool-style, cf. `Int213.neg_subNatNat`),
not a new operation.  "Inner product" `⟨f,g⟩ = Σ_x f(x)·g((n−x)%n)`-style
pairings are convolution-at-0 in disguise; Parseval is the convolution
theorem read on the diagonal.

## 3. Building Blocks

| Tool | File | Use |
|---|---|---|
| order-2 telescope + count form | `Lib/Math/NumberTheory/ModArith/CharacterOrthogonality.lean` | `charSumExp_eq_zero`, `qr_count_eq_nonqr_count` |
| general-order telescope in ℤ/p | `Lib/Math/NumberTheory/ModArith/CyclicCharacterOrthogonality.lean` | `geomNat_telescope`, `cyclic_orthogonality_modp` |
| orders 3, 6 in ℤ[ω] | `Lib/Math/Algebra/CayleyDickson/Integer/RootOfUnityOrthogonality.lean` | `geomSum_telescope`, `root_orthogonality` |
| order 4 in ℤ[i] | `Lib/Math/Algebra/CayleyDickson/Integer/GaussianOrthogonality.lean` | quartic leg |
| free group ring + convolution | `Lib/Math/Algebra/CayleyDickson/Integer/EisensteinGroupRing.lean` | `conv`, bilinearity, funext-free style |
| cubic Gauss sum scaffold | `Lib/Math/Algebra/CayleyDickson/Integer/EisensteinGaussSum.lean` | `gauss`, `gaussConj`, `conv_diag_index` |
| μ_n crystallographic cap | `Lib/Math/Algebra/CayleyDickson/Tower/CyclotomicTraceDegree.lean` | which n live in ℤ[ω]/ℤ[i] |
| Laplacian eigenvalue facts | `Lib/Math/Geometry/DiscreteCurvature/DiscreteLichnerowicz.lean` | `km_eigenvalue`, `km_meanzero_eigen` |
| closed reciprocity (target of re-reading) | `Lib/Math/NumberTheory/ModArith/QuadraticReciprocity.lean` | `quadratic_reciprocity`, `gauss_mu` |
| Zolotarev / dlog-parity character | `Lib/Math/NumberTheory/ModArith/{ZolotarevSign,DiscreteLogParity}.lean` | quadratic χ as parity Lens |
| bridge memo | `research-notes/frontiers/curvature_spectrum_crossdomain.md` | bridge 1 spec (FE) |

Suggested home: `lean/E213/Lib/Math/NumberTheory/Fourier/` (new
sub-cluster; ≥5 files ⟹ INDEX.md).

## 4. Phase Plan

### Phase FA — Characters + orthogonality consolidation (4-6 commits)

Goal: one generic character kernel; existing telescopes become instances.

1. `Fourier/CharGroup.lean` — `structure NthRoot (R) (n) : ζ, ζ^n = 1,`
   regularity witness (`∀ a, 0 < a → a < n → IsRegular (ζ^a − 1)` or the
   telescope hypothesis directly); `addChar (z : NthRoot R n) (a x : Nat) :
   R := z.ζ ^ ((a*x) % n)`.
2. Generic telescope, one statement subsuming the three copies:
   `theorem char_sum_zero (z : NthRoot R n) (ha : a % n ≠ 0) :`
   `sumRange n (fun x => addChar z a x) = 0`.
3. Full orthogonality relations (coefficient form):
   `theorem char_orthogonality : sumRange n (fun x => addChar z a x * addChar z (n - b%n) x) = if a % n = b % n then (n : R) else 0`.
4. Instances: ℤ (n=2, via `altSign`), `ZOmega` (n=3,6), `ZI` (n=4),
   ℤ/p-internal (n ∣ p−1, wrapping `cyclic_orthogonality_modp`), and the
   universal `R[C_n]` basis character.
5. Cross-cite: docstrings of the three legacy files point at the generic
   kernel (no deletion narration; content stays, engine deduped).

### Phase FB — DFT inversion + Parseval (4-6 commits)

1. `Fourier/DFT.lean` — `def dft (z) (f : Nat → R) (a : Nat) : R :=`
   `sumRange n (fun x => f x * addChar z a x)` (a coefficient function,
   never compared as a function).
2. Double-transform reflection (the inversion, multiply-through, pointwise):
   `theorem dft_dft (x : Nat) (hx : x < n) : dft z (dft z f) x = n * f ((n - x) % n)` — proof = swap the double sum (`sumZ_swap` pattern,
   `Linalg213/SumLinear`), inner sum killed by `char_orthogonality`.
3. `theorem dft_injective_pointwise : (∀ a, dft z f a = dft z g a) → ∀ x, x < n → f x = g x` (faithfulness of the Lens family; needs n regular in R —
   flag: over ℤ/ℤ[ω]/ℤ[i] this is `n ≠ 0`, free).
4. Parseval (diagonal pairing, conjugation = index reflection):
   `theorem parseval : sumRange n (fun a => dft z f a * dft z (fun x => g ((n - x) % n)) a) = n * sumRange n (fun x => f x * g ((n - x) % n))` —
   with the `f = g` corollary as the length statement (Plancherel).
5. Basis transforms pinned: `dft_delta`, `dft_const` (the two degenerate
   Lens readings: point ↦ flat, flat ↦ n·point).

### Phase FC — Convolution theorem + finite Poisson (4-6 commits)

1. Generalise `EisensteinGroupRing.conv` from `ZOmega`-coefficients to the
   generic carrier: `def conv (n) (f g : Nat → R) (k) := sumRange n (fun i => f i * g ((k + n - i % n) % n))` (one file; the Eisenstein one
   becomes the `R = ZOmega` instance — rule 7).
2. `theorem dft_conv (a) : dft z (conv n f g) a = dft z f a * dft z g a`
   — reindex the double sum along the group law; the count-Lens statement:
   convolution of counts reads as product of readings.
3. Parseval re-derived as `dft_conv` at the diagonal (records that §2.5
   was structural, not a coincidence).
4. Finite Poisson summation, subgroup–annihilator, multiply-through
   (for `d ∣ n`, `n = d·m`):
   `theorem poisson_finite (hd : n = d * m) : d * sumRange m (fun j => f (d * j)) = sumRange d (fun k => dft z f (k * m))` —
   the subgroup `dℤ/n` totalled on the left, its annihilator `mℤ/n` on the
   right.  Pure double counting; no measure, no limit.
5. Corollaries at `d = 1` and `d = n` reproduce `dft_const`/`dft_delta`
   (sanity ring).

### Phase FD — Gauss-sum re-reading + one reciprocity payoff (5-8 commits)

Quadratic reciprocity is CLOSED (Eisenstein lattice route).  FD does not
re-prove it; it exhibits the spectral reading and cashes one new theorem.

1. `Fourier/GaussSumDFT.lean` — the Gauss sum as a Fourier coefficient:
   `theorem gauss_is_dft : gaussSum χ z = dft z (fun t => χ t) 1` — for χ
   the quadratic character read as dlog parity (`DiscreteLogParity`),
   values in `{+1,−1} ⊆ R`.
2. Twist law (χ multiplicative, `gcd a p = 1`):
   `theorem dft_char_twist : dft z χ a = χinv a * gaussSum χ z` — the
   multiplicative character is its own transform up to the scalar `g(χ)`;
   this is the "self-dual Lens" fact, the whole spectral content of χ.
3. Norm identity (carrier = group ring, coefficient form; the quadratic
   sibling of the cubic `g·conj g = p·1 − N` already scaffolded in
   `EisensteinGaussSum`): `theorem gauss_mul_conj (k) : conv p (gauss χ) (gaussConj χ) k = if k = 0 then (p : R) - 1 else -1`-shaped, summing to
   `g(χ)·ḡ(χ) = p` on the invariant coefficient.
4. Payoff theorem (pick ONE, sized to close):
   `theorem gauss_sq_eq_signed_p : gaussSum χ z * gaussSum χ z = (if p % 4 = 1 then (p:R) else -(p:R))` in `R[C_p]` coefficient form —
   the classical `g² = (−1)^{(p−1)/2} p`, from 3 + the twist law.
5. Reconciliation note (theory tier, on promotion): the lattice-route
   `quadratic_reciprocity` and the Gauss-sum square are two Lenses on one
   count (`gauss_mu` is the shared joint); cite, don't re-derive.
   (Stretch: finish the cubic `N(J) = p` extraction riding the same
   `conv` engine — the open `EisensteinGaussSum` leg.)

### Phase FE — K_p spectrum bridge instantiation (3-5 commits)

Closes `curvature_spectrum_crossdomain.md` bridge 1.

1. `Fourier/CayleyLaplacian.lean` — the complete-shift Laplacian on ℤ/n
   over R (coefficient form): `def lap (n) (f : Nat → R) (x) := n * f x - sumRange n (fun y => f y)` (K_n = Cayley graph of ℤ/n on all
   non-zero shifts; matches `DiscreteLichnerowicz`'s `J − m·I` shape).
2. `theorem lap_char_eigen (ha : a % n ≠ 0) (x) : lap n (addChar z a) x = n * addChar z a x` — immediate from FA `char_sum_zero`: nontrivial
   characters are mean-zero, hence λ = n eigenfunctions.
3. `theorem char_meanzero_iff : sumRange n (addChar z a) = 0 ↔ a % n ≠ 0`
   — the trivial character is the λ = 0 line.
4. Tie to the curvature module at `n = p` prime: instantiate
   `km_meanzero_eigen` with the Int-valued order-2 character (`altSign` of
   dlog) and cross-cite `km_eigenvalue`; record that FB inversion = the
   eigenbasis is complete (the spectrum `{0, n}` has multiplicities
   `1, n−1` because the n character-Lenses jointly invert).
5. Update `curvature_spectrum_crossdomain.md` bridge 1 status →
   instantiated; frontier bookkeeping per PROCESS.md.

## 5. Success Criteria

- Every theorem ∅-axiom: `#print axioms` empty; audit via
  `tools/scan_axioms.py` per module.  No `funext` anywhere (all
  statements pointwise/coefficient equations).
- No ℚ, no ℝ, no continuous circle: carriers are ℤ, `ZOmega`, `ZI`,
  ℤ/p-internal residues, and free group-ring coefficients.  Every place a
  classical text divides by n, the n appears multiplied on the other side.
- One telescope engine (FA) with the three legacy orthogonality files as
  cited instances — no fourth copy.
- Closure set: `char_orthogonality`, `dft_dft`, `parseval`, `dft_conv`,
  `poisson_finite`, `gauss_sq_eq_signed_p`, `lap_char_eigen` all proven;
  bridge 1 of `curvature_spectrum_crossdomain.md` marked instantiated.
- On closure (H1-H4 + S1-S3): promote narrative to
  `theory/math/numbertheory/finite_fourier.md` (or a `fourier/` mirror),
  archive the working notes per `theory/PROMOTION_CRITERIA.md`.

## 6. Connections to Other Tracks

- **E1 Gram forcing (α_em)**: the normalised ℚ-cup consumes FA/FB kernels.
- **B1 quartic reciprocity**: rides the FD `conv`/Gauss-sum engine in ℤ[i].
- **Curvature/spectral track**: FE; further Cayley graphs (not just K_n)
  are the natural sequel.
- **Critical line / Dirichlet**: `DirichletConvolution` +
  multiplicative-χ DFT is the finite face of L-functions.

## 7. Open Problems

- General-n μ_n on one carrier: `R[C_n]` gives ζ as a basis vector, but
  `(ζ−1)`-regularity needs the cyclotomic-vs-finite-field reconciliation
  flagged in `CyclicCharacterOrthogonality` (the map `ℤ[ζ_n] → ℤ/p`, `ζ ↦ ω`).
- The `1/√n`-unitary normalisation (physics convention) needs the ℚ-cup
  plus a `Real213` cut for `√n` — deferred; the multiply-through form is
  the calculable operand (limit-deified row: the bracket IS the math).
- Fourier on (ℤ/n)^× for non-prime n — needs the totient-indexed
  character family; `TotientPairing` is the seed.

## 8. First Marathon Command

```
"Start Phase FA.  Create Lib/Math/NumberTheory/Fourier/CharGroup.lean:
generic NthRoot + addChar + char_sum_zero subsuming the three existing
telescopes, with instances for ZOmega (n=3,6), ZI (n=4), ℤ/p-internal."
```
