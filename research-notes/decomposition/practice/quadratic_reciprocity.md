# Decomposition: quadratic reciprocity

*213-decomposition of "the law of quadratic reciprocity" `(p/q)(q/p) = (−1)^((p−1)/2·(q−1)/2)`,
per `../README.md` (model v7.1). LEVERAGE attempt: does the calculus PREDICT the reciprocity sign as
the parity residue of ONE grid-permutation read two ways — consolidating `parity.md`'s
permutation-sign reading and `fourier.md`/`representation.md`'s character arrow into a deep theorem?*

The hypotheses under test (from the task):
1. the **Legendre symbol** `(a/p)` = the order-2 character (`parity.md`'s `L₂` = `det=±1` = `psign`);
2. **Zolotarev's lemma**: `(a/p)` IS the sign of the permutation `x↦ax mod p` — the Legendre symbol
   is *literally* the permutation-sign reading;
3. **quadratic reciprocity** = the sign of a single `m×n` lattice/permutation counted two ways — the
   `×↦{±1}` character read across two moduli, the `(−1)^…` factor = the parity residue of the grid swap;
4. Eisenstein's lattice-point count = the count-reading (`cardinality.md`) at a resolution; the
   reciprocity factor = its parity residue.

**Headline (the surprise, stated up front so the rest is honest):** unlike every prior leverage entry
where the *deep* theorem was a named open target, here **the full law of quadratic reciprocity is
already a strict ∅-axiom Lean theorem** — `QuadraticReciprocity.quadratic_reciprocity` (11 PURE,
`#print axioms` clean this session) — proved via *exactly* the Eisenstein lattice-double-count the
calculus predicts. So this is the rare entry where the calculus's prediction is **machine-confirmed at
the deepest leg**, not deferred. The decomposition's job is to show the proof's spine *is* the calculus's
two invariants (the `×↦{±1}` character + the parity residue) — and it is, term for term.

## The decomposition (C / Reading / Residue)

- **Construction `C` — two cyclic constructions and one product grid.** For distinct odd primes `p, q`
  the operands are the two half-systems `[1..m]` and `[1..n]` (`m=(p−1)/2`, `n=(q−1)/2`), which are
  `parity.md`'s `ℕ`-count truncated, carried on the multiplicative orbits `(ℤ/p)ˣ`, `(ℤ/q)ˣ`
  (`fourier.md`'s cyclic `C = ⟨g⟩`). The *joint* object is the **rectangle grid** `[1..m]×[1..n]` — the
  literal count-construction (`cardinality.md`) at resolution `(m,n)`. In Lean: `seg m`, `seg n`
  (`GaussLemma.seg`), and the grid is the doubly-summed `seg m × seg n` of `floor_sum_rectangle`.

- **Reading `L₂` — the order-2 character, read as a permutation sign.** `(a/p)` is `parity.md`'s `L₂`
  laid over the multiply-by-`a` permutation `σ_a : x ↦ a·x mod p`. The calculus's claim (hypothesis 2)
  is *literal and Lean-closed*: `ZolotarevMuBridge.zolotarev_mu` proves `psign σ_a = 1 ⟺ a` is a QR —
  the Legendre symbol IS the permutation sign — and `det_permMatrix_mulPermMod` proves `det(permMatrix
  σ_a) = (a/p)`. So `parity.md`'s collapse "parity = permutation-sign = `det=±1`" is realized *on the
  Legendre symbol itself*: one permutation `σ_a`, three readouts (inversions/`psign` · matrix `det` ·
  Legendre QR), all one number.

- **Residue — the parity bit `q=±1` of the grid swap.** The reading `L₂` forgets everything about `σ_a`
  except one bit; reciprocity is the statement that *the same bit*, computed for `σ_q` mod `p` and `σ_p`
  mod `q`, is forced to agree or disagree by **one** number: the parity of the grid count `m·n`. The
  residue of the count-reading on the grid — what the cardinality `m·n` forgets down to its last bit —
  **IS** the reciprocity factor `(−1)^{mn}`. This is `golden_ratio.md`/`cardinality.md`'s `q=±1` residue
  tag in its sharpest finite incarnation: the residue here is *exactly one sign bit*, and that bit is
  the whole content of the deepest theorem in elementary number theory.

## Re-seeing

```
   Legendre symbol (a/p)   =  ⟨ σ_a : x↦ax mod p  |  L₂ = psign ⟩            (zolotarev_mu: psign σ_a = (a/p))
                           =  ⟨ permMatrix σ_a    |  det ⟩                    (det_permMatrix_mulPermMod = (a/p))
   Gauss's lemma           =  (a/p) = ∏_{x∈[1,m]} sgFn(a·x)  = (−1)^μ         (gauss_qr; psign_mulPermMod_eq_prodSgn)
   Eisenstein's lemma      =  (a/p) ⟺ Σ_{x∈[1,m]} ⌊a·x/p⌋ even               (floor_qr)
   the grid (one count)    =  Σ_x⌊qx/p⌋ + Σ_y⌊py/q⌋ = m·n                     (floor_sum_rectangle)
   QUADRATIC RECIPROCITY   =  ((q/p)=(p/q)) ⟺ m·n even                        (quadratic_reciprocity)
```

The chain is: **one permutation sign** (`psign σ_a`) `=` **a least-residue sign product** (`∏ sgFn`,
Gauss's lemma) `=` **a floor-sum parity** (`Σ⌊ax/p⌋`, Eisenstein) — and the floor-sums for the two
directions are the **two ways of counting the one grid** `[1..m]×[1..n]` split by its diagonal
`q·x = p·y`. The reciprocity sign is the parity of that single count `m·n`.

### The grid counted two ways (the load-bearing diagram)

```
   y∈[1,n]                                  Σ_x ⌊qx/p⌋   = # points BELOW the diagonal  (per column x)
     │   · · · · · · · · /                  Σ_y ⌊py/q⌋   = # points ABOVE the diagonal  (per row y)
     │   · · · · · · / ·                     ─────────────────────────────────────────
     │   · · · · / · · ·                     SUM           = every point of the grid      (no point ON it,
     │   · · / · · · · ·                                                                   since p∤q·x: elem_tri)
     │   / · · · · · · ·                                  = m · n
     └─────────────────  x∈[1,m]
         diagonal q·x = p·y
```

`floor_sum_rectangle` is the calculus's hypothesis 3 made into a ∅-axiom theorem: the grid is counted
once, read two ways (column-floors below the diagonal = `Σ⌊qx/p⌋`, row-floors above = `Σ⌊py/q⌋`), and
their sum is the total `m·n` because **no lattice point sits on the diagonal** — `elem_tri` proves
exactly one of `p·y < q·x`, `q·x < p·y` holds (the equality `q·x = p·y` would force `p ∣ q·x`,
impossible for the coprime primes). That "exactly one of two, never the boundary" is the `q=±1`
direction bit of `C` (`homology.md`'s orientation, `integers.md`'s swap) read on the antisymmetric grid
relation `<` — the trichotomy collapses to a clean two-way split *because* the diagonal is empty.

## LEVERAGE — does the calculus PREDICT the reciprocity sign as the parity residue? **YES — and it is Lean-closed.**

**Honest verdict: PREDICTION (the strongest in the notebook so far) — the calculus derives QR's
reciprocity sign as the parity residue of a single grid counted two ways, and the *full theorem* is
already strict ∅-axiom Lean, not a named open target.** This is stronger than `fourier.md`
(orthogonality predicted, then closed) and `representation.md` (consolidation): here the deepest leg —
the reciprocity law itself — is *machine-checked*, and its proof's three load-bearing steps are *exactly*
the calculus's predicted decomposition.

### Leg 1 — the Legendre symbol IS the permutation-sign reading. **PREDICTION, Lean-closed (universal).**
Hypothesis 2 (Zolotarev) is not analogy: `zolotarev_mu` proves `psign(mulPermMod a p) = 1 ⟺ a` QR for
**every** odd prime, and `det_permMatrix_mulPermMod` gives the determinant form. `parity.md`'s
collapse — parity `=` permutation-sign `=` `det=±1` — is realized *on the Legendre symbol*: the
order-2 character is the sign of `σ_a`, three readouts of one permutation. The forced mechanism:
`psign_mulPermMod_eq_prodSgn` shows `psign σ_a = prodZ(map sgFn)` — the permutation sign *equals* the
least-residue sign product, i.e. **Zolotarev's lemma and Gauss's lemma are the same `±1` readout of the
same fold**. This is `parity.md` + `fourier.md`/`representation.md`'s `×↦·` arrow (`psign_mulPerm_hom`:
the sign is a homomorphism) fused.

### Leg 2 — reciprocity = ONE grid counted two ways. **PREDICTION, Lean-closed.**
Hypothesis 3 is `floor_sum_rectangle` (PURE): `Σ⌊qx/p⌋ + Σ⌊py/q⌋ = m·n`. The two floor-sums are the two
*directions* of the same `×↦{±1}` character — `(q/p)` reads `L₂` of `σ_q` mod `p`, `(p/q)` reads `L₂` of
`σ_p` mod `q` — and they are bound by a single count of the joint grid. The calculus *predicted* the
reciprocity factor would be "the `q=±1` residue of the swap"; `parity_sum_iff` proves precisely that:
with `S + T = m·n`, the two parities `2∣S`, `2∣T` agree **iff `m·n` is even**. The reciprocity sign is
*the parity residue of the cardinality `m·n`* — hypothesis 4, verbatim, machine-checked.

### Leg 3 — Eisenstein = the count-reading at a resolution; the factor = its parity residue. **PREDICTION, Lean-closed.**
`floor_qr` is Eisenstein's lemma: `(a/p) ⟺ Σ_{x∈[1,m]} ⌊a·x/p⌋` even — the Legendre symbol is the
*parity of a lattice-point count* (`⌊a·x/p⌋` = points under the line of slope `a/p` over column `x`).
This is `cardinality.md`'s count-reading at resolution `(m, p)`, its residue taken mod 2. The bridge
`floor_qr` is welded to Gauss's lemma through the *shared `sgFn`*: `floor_mu_even` proves
`2 ∣ (Σ⌊ax/p⌋ + μ)` where `μ = countNeg(map sgFn)` is the Gauss sign-flip count — so "floor-sum parity"
and "sign-product parity" are one parity. The calculus's "Eisenstein floor-count = count-reading,
factor = parity residue" is not a re-description; it is the literal structure of `floor_qr` ∘
`floor_sum_rectangle` ∘ `parity_sum_iff`.

### Does it consolidate `parity.md` + the character arrow? **YES — decisively, and at maximal depth.**
The `×↦{±1}` / `×↦·` character arrow now provably runs through QR's spine: `psign_mulPerm_hom` (the sign
is multiplicative — `parity.md`/`fourier.md`'s arrow) gives `(ab/p)=(a/p)(b/p)`; `psign_mulPermMod_eq_prodSgn`
fuses the permutation-sign reading with Gauss's `±1`-product; and the reciprocity sign falls out as the
parity residue (`q=±1` tag) of the grid count. So **the deepest theorem of elementary number theory is the
order-2 character + the parity residue, read across two moduli on one grid** — the calculus's two
load-bearing invariants (the character arrow, the `q=±1` residue) at their highest-payoff joint. The
single permutation `σ_a` carries: an inversion-count (`psign`), a matrix determinant (`det_permMatrix`),
a Legendre symbol (`zolotarev_mu`), a least-residue sign product (`gauss_qr`), and — via the grid — the
reciprocity law itself. Five readouts, one construction.

## Revelation (forcing + collapse)

**The residue surfaced is this: quadratic reciprocity has no content beyond the parity of a single
number `m·n`, and that number is the cardinality of one grid the two Legendre symbols read from
opposite sides.** What classical number theory presents as a deep, near-miraculous relation between two
unrelated primes is, in the calculus, **forced**: the same `×↦{±1}` character read on `σ_q` mod `p` and
on `σ_p` mod `q` are bound by `Σ⌊qx/p⌋ + Σ⌊py/q⌋ = m·n` (one grid, no diagonal point, `elem_tri`), so
their signs can only agree or disagree according to *one parity bit* — the `q=±1` residue of `m·n`. The
collapse is fivefold and **fully ∅-axiom certified**: the Legendre symbol, the permutation sign, the
matrix determinant, Gauss's least-residue sign product, and Eisenstein's lattice floor-count are **one
order-2 character read five ways**, and quadratic reciprocity is that character's parity residue counted
across the product grid. The "miracle" is the emptiness of the diagonal.

The honest contrast with the rest of the notebook: prior leverage entries (`fourier.md`, `gaussian_clt.md`,
`noether.md`, `representation.md`) *predicted* a deep form and named the Lean target left open. Here the
deep form — the reciprocity law — is **closed**, and the proof Lean actually runs is the Eisenstein
lattice double-count the calculus names as its prediction. This is the calculus's prediction confirmed at
the deepest leg, not deferred.

## Touches on model v7.1? **No new primitive — EXTEND by the deepest consolidation + one Lean-closed deep leg.**

The two invariants (character arrow, `q=±1` residue) and four axes (direction, fold-height,
resolution+base, iteration-character) absorb QR with nothing added. It is `parity.md`'s `L₂` /
`fourier.md`'s order-2 character, read on the multiply-by-`a` permutation (`zolotarev_mu`), with the
reciprocity factor = the `q=±1` parity residue of the resolution-`(m,n)` count-grid (`cardinality.md` +
`integers.md`'s swap bit, via the empty-diagonal trichotomy `elem_tri`). The one note worth the README's
batch log:

> **Quadratic reciprocity is the order-2 character's parity residue read across two moduli on one grid —
> and unlike every prior deep-leverage target, the full law is already strict ∅-axiom Lean
> (`quadratic_reciprocity`, 11 PURE). The Eisenstein lattice double-count `floor_sum_rectangle`
> (`Σ⌊qx/p⌋+Σ⌊py/q⌋=m·n`) is the calculus's "one count, two readings" prediction made a theorem; the
> reciprocity sign is `parity_sum_iff`'s parity bit of `m·n` (the `q=±1` residue). The single permutation
> `σ_a` carries five readouts (psign / det / Legendre / Gauss sign-product / Eisenstein floor-count),
> all one. The empty diagonal (`elem_tri`: no `q·x=p·y` for coprime primes) is where the "miracle" lives.**

This sharpens, does not alter, model v7.1: QR is the highest-payoff joint of the two invariants, and the
rare entry where the deepest leg is Lean-closed rather than a named open target.

## Verified Lean anchors (grep + `#print axioms` via `tools/scan_axioms.py`, this session)

| Leg | Theorem (file:line) | Purity |
|---|---|---|
| ★★★★★ **quadratic reciprocity (full law)** | `Lib/Math/NumberTheory/ModArith/QuadraticReciprocity.lean:461` `quadratic_reciprocity` | **11 PURE / 0 DIRTY** (scan, this session) ✓ |
| ★★ grid counted two ways (hypothesis 3) | `…/QuadraticReciprocity.lean:350` `floor_sum_rectangle` `Σ⌊qx/p⌋+Σ⌊py/q⌋=m·n` | PURE (in the 11) ✓ |
| empty diagonal (the `q=±1` two-way split) | `…/QuadraticReciprocity.lean:334` `elem_tri` (exactly one of `p·y<q·x`, `q·x<p·y`) | PURE (in the 11) ✓ |
| ★ Eisenstein lemma (count-reading, hyp 4) | `…/QuadraticReciprocity.lean:223` `floor_qr` `(a/p)⟺Σ⌊ax/p⌋ even` | PURE (in the 11) ✓ |
| floor-sum ≡ Gauss μ (welds Eisenstein↔Gauss) | `…/QuadraticReciprocity.lean:128` `floor_mu_even` `2∣(Σ⌊ax/p⌋+μ)` | PURE (in the 11) ✓ |
| ★ reciprocity sign = parity residue of `m·n` | `…/QuadraticReciprocity.lean:423` `parity_sum_iff` `(2∣S↔2∣T)↔N%2=0` | PURE (in the 11) ✓ |
| generalized QR-criterion (apply at other prime) | `…/QuadraticReciprocity.lean:204` `gauss_mu_gen` | PURE (in the 11) ✓ |
| ★★★★★ **Zolotarev: `psign σ_a = (a/p)` (hyp 2)** | `Lib/Math/NumberTheory/ModArith/ZolotarevMuBridge.lean:229` `zolotarev_mu` | **14 PURE / 0 DIRTY** (scan, this session) ✓ |
| ★★★★★ Zolotarev as determinant `det(permMatrix σ_a)=(a/p)` | `…/ZolotarevMuBridge.lean:240` `det_permMatrix_mulPermMod` | PURE (in the 14) ✓ |
| sign-reading = Gauss `±1`-product (fuses them) | `…/ZolotarevMuBridge.lean:216` `psign_mulPermMod_eq_prodSgn` `psign σ_a = ∏ sgFn` | PURE (in the 14) ✓ |
| `psign σ_a` = diagonal/μ count | `…/ZolotarevMuBridge.lean:164` `psign_mulPermMod_eq_diag`; `:202` `altSign_diag_eq_prodSgn` | PURE (in the 14) ✓ |
| ★★★★★ Gauss's lemma `(a/p)=∏sgFn=(−1)^μ` | `Lib/Math/NumberTheory/ModArith/GaussLemma.lean:431` `gauss_qr` | ∅-axiom (in `GaussLemma`; deps of the 11/14 PURE scans) ✓ |
| the fold `x↦±(ax mod p)` is a permutation of `[1,m]` | `…/GaussLemma.lean:263` `fold_perm` (`:129` `def fold`, `:329` `def sgFn`) | ∅-axiom ✓ (grep-confirmed) |
| Gauss core `aᵐ ≡ ∏ signs (mod p)` | `…/GaussLemma.lean:347` `gauss_core` | ∅-axiom ✓ (grep-confirmed) |
| Gauss μ-criterion `QR ⟺ μ even` | `Lib/Math/NumberTheory/ModArith/SecondSupplement.lean:216` `gauss_mu` (`:35` `def countNeg`) | ∅-axiom ✓ (grep-confirmed) |
| sign character is multiplicative (`×↦·` arrow) | `Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133` `psign_mulPerm_hom`; `:106` `mulPerm_comp` | ∅-axiom ✓ (grep-confirmed; per `parity.md`/`fourier.md`) |
| order-2 char = QR/dlog (`L₂` = Fourier char) | `Lib/Math/NumberTheory/ModArith/DiscreteLogParity.lean:95` `qr_pow_iff_even_exp`; `:123` `dlog_exists` | ∅-axiom ✓ (grep-confirmed; per `fourier.md`) |
| primitive root exists (cyclic `C` inhabited) | `Lib/Math/NumberTheory/ModArith/PrimitiveRoot.lean:156` `exists_primitive_root` | ∅-axiom ✓ (grep-confirmed) |
| χ-orthogonality (the Σχ=0 sibling, order 2) | `Lib/Math/NumberTheory/ModArith/CharacterOrthogonality.lean:146` `quadratic_orthogonality`; `:220` `qr_count_eq_nonqr_count` | ∅-axiom ✓ (grep-confirmed; per `fourier.md`) |
| `det(permMatrix σ)` machinery | `Lib/Math/Algebra/Linalg213/PermMatrixDet.lean:177` `det_permMatrix`; `:39` `permMatrix` | ∅-axiom ✓ (grep-confirmed) |

## Conceptual-only legs / honest residue boundary

QR is the rare entry with **no missing deep leg** — the full law, Zolotarev, Gauss's lemma, Eisenstein's
lemma, and the lattice double-count are all strict ∅-axiom Lean. The honest residue boundary is only at
the *adjacent* unbuilt pieces, none of which QR's theorem needs:

- **The `(−1)^…` is encoded as `m·n even ⟺ signs agree`, not as a literal `(−1)^{((p−1)/2)((q−1)/2)}`
  power.** `parity_sum_iff` carries the sign bit as a parity-of-product `%2=0`, which is the calculus's
  `q=±1` residue in its honest finite form (`fourier.md`'s `Real213`-cut `ζ` is *not* invoked, and need
  not be — the order-2 character lives entirely in `{±1}`, no transcendental cut). This is a *feature*,
  not a gap: the `(−1)^k` notation is the count-Lens reading of "parity", and the Lean keeps the count.
- **The two supplements** (`(−1/p)` first supplement `EulerFirstSupplement`; `(2/p)` second supplement
  `SecondSupplement.second_supplement`, `p ≡ ±1 mod 8`) exist separately and are the `a=−1`, `a=2`
  *non-coprime-to-the-odd-prime* edge cases the main law's coprime-odd-primes hypothesis excludes — same
  Gauss-lemma machinery, not part of `quadratic_reciprocity`'s statement. Present, not missing.
- **The full Gauss SUM `Σ χ(x) ζ^x`** (the analytic route, additive character `ζ^x` against the
  multiplicative character) remains a `Real213`/`ℤ[ω]` cyclotomic-cut object as `fourier.md` located —
  but the repo's QR proof takes the **Eisenstein lattice route instead**, which is fully finite, so the
  Gauss-sum residue is *not on the critical path*. The "Gauss lemma vs Gauss sum" distinction
  `fourier.md` flagged is the right one: the repo proved QR through Gauss's *lemma* (`gauss_mu`,
  combinatorial), not the *sum* (analytic) — and the lemma route needs no cut.
