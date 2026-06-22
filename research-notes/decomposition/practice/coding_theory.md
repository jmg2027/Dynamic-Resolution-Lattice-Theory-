# Decomposition: coding theory / error-correcting codes (linear codes, H/G, syndrome, Hamming codes, minimum distance, syndrome decoding, Singleton/Hamming bounds, MDS)

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`, the REVELATION
rule) and `../SYNTHESIS.md` (the two invariants — the character arrow, the `q=±1` residue tag — and the
`q=±1` spine). Neighbors: `homology.md` (the `ker δ/im δ` residue), `parity.md`/`game_theory.md`
(the 𝔽₂/XOR character), `fourier.md`.*

*The thesis tested: **a linear code is the calculus's parity character read as a cochain complex.** The
parity-check matrix `H` is a coboundary operator `δ`; the code `C = ker H` is the cocycles (the SAME
`ker δ` as `homology.md`); the syndrome `s = Hx` is the cohomology class (the residue of `x` mod the
code, `ker δ/im` read on received words); minimum distance / Hamming weight = the smallest nonzero
cocycle (`betti_one_cycle`'s nonzero class); syndrome decoding (`s=0 ⟺ codeword`) = the `q=±1` tag
(`s=0`/in-code = `q=+1` exact pole, `s≠0`/error-detected = `q=−1` escape, `nonzero_cohomology_class`).
So a code = 𝔽₂ parity character + the `ker δ` cocycle reading + the `q=±1` syndrome-zero/nonzero tag —
no new primitive. **The unusual datum: the named field object is BUILT ∅-axiom**, not absent.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **graph/simplex as an 𝔽₂ cochain complex** = `homology.md`'s `C` exactly. The
  load-bearing in-repo instance is the K₅ complex: vertices `Spin = Fin 5 → Bool`, edges
  `Coupling = Fin 10 → Bool` (one bit per edge), triangles `TriCochain = Fin 10 → Bool` (10 faces). This
  is the bare iterated distinguishing read at two height-strata (vertex/edge/triangle), carrying the
  README's two read-off axes: **fold-height** (cochain degree `0→1→2`) and the **direction/orientation
  bit** (the XOR sign collapsing `(−1)^i` to Bool in 𝔽₂, `homology.md`'s direction sub-readout). A code's
  ambient space `𝔽₂ⁿ` = the edge cochains `C¹`.

- **Reading `L↓` (the parity-check coboundary)** — `H = δ`: project a word to its faces' XOR-parities.
  In-repo: `delta1 : Coupling → TriCochain` (`SpinGlass.lean:87`), `δ₁ J(t) = XOR of J over the 3 edges
  of triangle t` — *literally the parity-check matrix* (each triangle = one parity-check row). The
  generator side is `delta0 : Spin → Coupling` (`:79`), `δ₀ σ(e) = σ(src e) ⊕ σ(tgt e)` — the
  generator matrix `G`, whose image is the codewords. `δ₁ ∘ δ₀ = 0` (the cancellation
  `(σi⊕σj)⊕(σj⊕σk)⊕(σi⊕σk)=0`, `homology.md`'s `∂²=0` as the orientation bits cancelling) is exactly
  `H·Gᵀ = 0` — the defining relation of a linear code. This `δ`/`δ`-pair IS the same height-reading run
  in the two directions homology already owns; `H` is not a new object, it is `δ` named in another course.

- **Residue (`q=±1` tag)** — the syndrome `s = Hx = δ₁ x`, read by `cocycleObstruction`
  (`SpinGlass.lean:113`, the weight-count of `δ₁ J`). Two stratified poles:
  - **`s = 0` ⟺ `q=+1` (converge / exact / in the code).** `x ∈ ker δ₁ = ker H`; codewords are the
    cocycles. On this contractible-style complex `ker δ₁ = im δ₀` (the K₅ code: every cocycle is a
    coboundary), so `s=0` ⟺ `x` is a genuine codeword `δ₀ σ` — the empty residue, `homology.md`'s
    `reduced_betti_d4_contractible` pole. Verified: `cocycleObstruction c₁ = 0`, `cocycleObstruction c₂ = 0`
    (`MLDecoder.lean:130-131`) for transmitted codewords; `cocycleObstruction (delta0 σ) = 0` universally
    (`spin_glass_213_capstone`, `SpinGlass.lean:136-139`) = `H·Gᵀ=0`.
  - **`s ≠ 0` ⟺ `q=−1` (escape / error detected).** A received `x` with `δ₁ x ≠ 0` is *not* a cocycle:
    the parity-check forces a value (the syndrome) the code's image cannot capture — `homology.md`'s
    `q=−1` obstruction residue, `NonzeroBetti.nonzero_cohomology_class`. Verified: a 1-bit channel error
    gives `cocycleObstruction (flipBit c₁ e) = 3` (`MLDecoder.lean:152-154`) — a nonzero syndrome = a
    surfaced cohomology class. **Syndrome decoding is reading this `q=±1` tag.**

## Re-seeing — `⟨C | L⟩ ⊕ Residue(q=±1)`

```
  ambient 𝔽₂ⁿ        =  ⟨ graph/simplex edge-cochains C¹ | — ⟩            (homology.md's C, edge stratum)
  generator G        =  δ₀ : C⁰ → C¹  (delta0; G's image = codewords)      (height-reading, raising)
  parity-check H     =  δ₁ : C¹ → C²  (delta1; H = the coboundary δ)       (height-reading, lowering; H = δ)
  code C = ker H     =  the cocycles ker δ₁  (= im δ₀ here: H·Gᵀ=0)        (the SAME ker δ as homology.md)
  H·Gᵀ = 0           =  δ₁∘δ₀ = 0  (XOR cancellation)                       (∂²=0, q=±1 bits cancel pairwise)
  syndrome s = Hx    =  δ₁ x = cocycleObstruction  (the cohomology class)   (residue of x mod the code)
  s = 0 ⟺ codeword   =  x ∈ ker δ₁  (the q=+1 exact pole, residue empty)    (reduced_betti contractible pole)
  s ≠ 0 ⟺ error      =  x ∉ ker δ₁  (the q=−1 escape, class surfaces)       (nonzero_cohomology_class)
  min distance d     =  min Hamming weight of a nonzero codeword            (smallest nonzero cocycle = betti_one_cycle)
  syndrome decoding  =  argmin Hamming dist to a codeword = ground state    (decodeML = ML = ground-state finder)
```

The K₅ code's parameters are a `[10, 4, 4]` linear code, all `decide`-verified (`MLDecoder.lean`):
`codeLength=10` (n), `codeDim=4` (k = NS+NT−1 = 5−1), `numCodewords=16` (2⁴), `minDistance=4` (d),
`correctableErrors = (d−1)/2 = 1`. The **Hamming (sphere-packing) bound** is verified as
`1 + codeLength ≤ 2^(codeLength − codeDim)` (`ml_decoder_capstone`, `MLDecoder.lean:126`:
`1+10 ≤ 2^6 = 64`). **Syndrome decoding** is `decodeML : Coupling → Fin 32` (`:68`), the argmin of
Hamming distance = the spin-glass ground-state finder (Sourlas 1989); `decodedCodeword (flipBit c₁ e) = c₁`
for every single-bit error (`MLDecoder.lean:148-150`) — 1-error correction, machine-checked.

Set beside `homology.md`'s triangle, coding theory consumes the **identical** two axes of `C`:

| reading | axis of `C` | readout | coding-theory name |
|---|---|---|---|
| `δ₀` (`delta0`) | height (raise, `C⁰→C¹`) | codewords = `im δ₀` | generator matrix `G` |
| `δ₁` (`delta1`) | height (lower, `C¹→C²`) ⊗ direction (XOR sign) | the syndrome `δ₁ x` | parity-check matrix `H` |
| residue `ker δ₁/im δ₀` | both | `s=0`/`s≠0` (`q=±1`) | the code `C` / the error |

So `H = δ` term-for-term; the syndrome IS `homology.md`'s cochain residue, read on received words.

## Revelation (collapse + forcing + the `q=±1` spine)

**Collapse — a linear code, a cochain complex, and a spin-glass ground-state problem are ONE
`⟨C|L⟩⊕Residue`.** The repo's `SpinGlass`/`MLDecoder` files prove this *as a single object* read three
ways: the K₅ frustration cochain complex (`δ₀`, `δ₁`, `δ₁∘δ₀=0`), the `[10,4,4]` ℤ/2-linear code
(generator `δ₀`, parity-check `δ₁`, syndrome `cocycleObstruction`), and the ML decoder (ground-state
finder). Coding theory's `(G, H, syndrome)` triple is `homology.md`'s `(δ₀, δ₁, ker δ₁/im δ₀)` triple in
another course's vocabulary — *no new primitive*. The Sourlas bridge the file builds (`MLDecoder.lean:8`)
is exactly this collapse made into a verified theorem: error-correction = cohomology = combinatorial
optimization, one `(C, L)`.

**Forcing — `H·Gᵀ = 0` is `δ²=0` is the `q=±1` orientation cancellation.** The defining law that
codewords have zero syndrome (`δ₁(δ₀ σ) = 0`) is NOT a design axiom; it is `homology.md`'s `∂²=0`, the
XOR-cancellation `(σi⊕σj)⊕(σj⊕σk)⊕(σi⊕σk)=0` — the README's `q=−1` direction-bit cancelling pairwise
(`dsq_zero_universal_delta4`'s shape, here `spin_glass_213_capstone:136-139` verifies
`cocycleObstruction(δ₀ σ)=0` over the test spins). So "every codeword passes every parity check" is
*forced* by the complex being a complex; the parity-check matrix exists *because* `δ` is a height-reading
whose two-step composite annihilates.

**The 𝔽₂ character — coding theory is `parity.md`/`game_theory.md`'s XOR character in its 𝔽₂ⁿ form.** The
whole ambient `(𝔽₂ⁿ, ⊕)` is `game_theory.md`'s nim-sum group: the pointwise-XOR group `C2_6.mul`
(`AutKGroup.lean:82`, `Fin 6 → Bool`, each element self-inverse), and the syndrome map `δ₁` is linear
over XOR — the same character homomorphism `BoolXORFold.psiNatPos_linear` (`:38`, 6/0 PURE):
`Ψ(v⊕w)=Ψ(v)⊕Ψ(w)`. Error linearity `s(x⊕e) = s(x)⊕s(e) = s(e)` for a codeword `x` (the syndrome depends
only on the error, the cornerstone of syndrome decoding) is *this* homomorphism. The {±1}-valued sibling
is `parity.md`/Zolotarev's `psign_mulPerm_hom` (`Zolotarev.lean:133`); coding theory is that arrow read
in 𝔽₂ⁿ instead of {±1}. The same PURE/DIRTY boundary `game_theory.md` pins applies: the per-bit
`Bool.xor` syndrome is PURE; a packed `Nat.xor` would be DIRTY (`AutKGroup.lean:71`) — the
Heyting/Boolean line on the central arrow, here on the syndrome map.

**The `q=±1` spine — syndrome-zero/nonzero IS the residue tag.** Minimum-distance decoding's `s=0 ⟺
codeword` is the spine verbatim: `s=0` = `q=+1` converge (`x ∈ ker δ`, the exact/in-code pole, residue
empty, `golden_is_converge`'s pole, `ResidueTag.lean:180`); `s≠0` = `q=−1` escape (`x ∉ ker δ`, the
parity-check forces a class outside the code's image — `nonzero_cohomology_class`,
`NonzeroBetti.lean:143`, the same `OneDiagonal`-flavoured "value outside the image"). The K₅ instance
makes the contrast a theorem: `cycle_vs_contractible_qpm` (`NonzeroBetti.lean:173`) tags the obstruction
class `escape` (`multiplier = −1`) and the contractible/exact case `converge` (`+1`). A detected error =
a non-contractible cocycle; a codeword = the contractible (residue-empty) case.

**Minimum distance = the smallest nonzero cocycle.** `d = min Hamming weight of a nonzero codeword`
(`minDistance=4`, K₅: `d = 1·(NS−1) = 4`) is the size of the *smallest nonzero element of the
residue/code* — `betti_one_cycle`'s nonzero-class weight on the hollow complex (`NonzeroBetti.lean:111`:
`im δ⁰ ⊊ ker δ¹`, a class survives). The error-correction radius `⌊(d−1)/2⌋` (the sphere-packing /
Hamming bound) is the resolution at which distinct cocycle-cosets stay separated — `homology.md`'s
residue read with a *weight* (Hamming weight = `L`'s weight parameter, `measure.md`/`entropy.md`'s axis).

**Singleton bound / MDS — the height/weight trade-off, predicted not built as a named object.** The
Singleton bound `d ≤ n − k + 1` and MDS codes (equality) are the statement that a code's minimum
distance (smallest-nonzero-cocycle weight) is capped by its codimension (`n−k` = `dim C² − ` reachable =
the number of independent parity checks = `dim im δ₁`). In the calculus this is the bidirectional
fold-height bookkeeping: `dim ker δ₁ + dim im δ₁ = n` (rank–nullity = the count-reading split), so
`k = dim ker δ₁` and the check-count `n−k` bound the achievable residue weight. The repo verifies the
*Hamming* (sphere-packing) bound concretely (`ml_decoder_capstone:126`) but the **Singleton bound and a
named `MDS` predicate are ABSENT** (grep-confirmed below) — predicted-not-built, a weight/height-count
identity the rank–nullity machinery would close.

## Note for the technique — does coding theory VALIDATE the calculus?

**EXTEND by consolidation, and stronger than predicted: the named field object is BUILT ∅-axiom.** Unlike
`game_theory.md`/`surreal.md`/`knots.md` (where the named object was the missing leg), coding theory's
central object — a linear code with a generator `δ₀`, a parity-check `δ₁ = H`, a syndrome
`cocycleObstruction`, minimum distance, the Hamming bound, and a verified ML syndrome decoder — exists in
`lean/E213` as a STRICT ∅-axiom module (`MLDecoder.lean` 13/0, `SpinGlass.lean` 13/0). Reasons it is
confirmation, not stress:

1. **No new axis.** `C` = `homology.md`'s cochain complex; `H = δ₁`, `G = δ₀` are the height-reading run
   in both directions (no new operator); the ambient 𝔽₂ⁿ = `game_theory.md`'s XOR character group
   (`C2_6.mul`, `psiNatPos_linear`); the syndrome = `homology.md`'s `ker δ/im δ` residue read on received
   words; `s=0`/`s≠0` = the formal `q=±1` tag (`cycle_vs_contractible_qpm`). The model v7.1 carrier covers
   all of it.
2. **It cashes the homology⇄physics⇄optimization triple as a theorem.** The Sourlas identity (ML
   decoding = spin-glass ground state = cohomology) is the deepest collapse here, and the repo proves it
   as one object read three ways — error-correction, frustration, and `ker δ/im δ` are `⟨C|L⟩` once. This
   is the re-skin-guard-passing revelation: a *verified collapse*, not a re-description.
3. **It lands the central arrow on its purity boundary.** The syndrome is the 𝔽₂ⁿ character; PURE
   per-bit (`delta1` over `Bool.xor`), DIRTY packed (`Nat.xor`) — the same Heyting/Boolean line.

**Honest residuals (predicted-not-built).** (i) A **general/abstract `LinearCode` type** with arbitrary
`n,k` over 𝔽₂ (or 𝔽_q) is ABSENT — only the concrete K₅ `[10,4,4]` instance is built; the *structure* is
general (`δ`/`H` is generic), the *named parametric object* is not. (ii) **Hamming codes** `[2^m−1, 2^m−1−m, 3]`
as a family, and the **Hamming bound in general `n,k,d`** (only the K₅ numeric instance is verified),
are absent. (iii) The **Singleton bound `d ≤ n−k+1`** and a named **MDS** predicate are absent — a
rank–nullity/weight-count identity the calculus predicts but no theorem states. (iv) **Reed–Solomon /
BCH / LDPC** (`MLDecoder.lean:104-108` names them as industry context only) need 𝔽_q with `q>2` and the
`Real213`/polynomial-evaluation machinery — the `q>2` analogue of `game_theory.md`'s 𝔽₂ ceiling. (v) A
**general minimum-distance theorem** (`d` = min nonzero weight over *all* codewords) is verified only at
concrete codewords by enumeration (`MLDecoder.lean:36`, the full enumeration is Rust-side); the
`∀`-quantified statement over an abstract code is the same arbitrary-cover/`∀S` quantifier
`measure.md`/`topology.md` locate as the finite-`List` setting's limit.

**Verdict: EXTEND (consolidation) + the named object BUILT.** A linear code = `homology.md`'s cochain
complex with `H = δ₁` (parity-check), `G = δ₀` (generator), `code = ker δ₁ = im δ₀` (cocycles), syndrome
`= cocycleObstruction = δ₁ x` (the cohomology class / residue of `x` mod the code), `H·Gᵀ=0 = δ²=0` (the
`q=±1` cancellation), minimum distance = the smallest nonzero cocycle weight (`betti_one_cycle`),
syndrome decoding `s=0/s≠0` = the formal `q=±1` tag (`cycle_vs_contractible_qpm`), and the ambient 𝔽₂ⁿ =
`parity.md`/`game_theory.md`'s XOR character (`psiNatPos_linear`, `C2_6.mul`). No new primitive; the
syndrome IS the calculus's `ker δ/im δ` residue applied to 𝔽₂ words with `H` as `δ`. The unusual datum:
the field's central object (code + parity-check + syndrome + ML decoder + Hamming bound + 1-error
correction) is a STRICT ∅-axiom theorem in-repo (`ml_decoder_capstone`), so coding theory is a *closed*
consolidation, with only the parametric family objects (general `LinearCode`, Hamming family, Singleton/MDS,
RS/BCH) predicted-not-built.

---

### Verified Lean anchors (file : line : theorem) — all grep-confirmed; scan tallies via `tools/scan_axioms.py`

- `Lib/Math/Cohomology/HodgeConjecture/Bridge/MLDecoder.lean` (**13/0 PURE**) — the `[10,4,4]` linear code +
  ML syndrome decoder:
  - `:60-64` `codeLength=10` (n), `codeDim=4` (k), `numCodewords=16`, `minDistance=4` (d),
    `correctableErrors=(d−1)/2=1` — the code parameters.
  - `:68` `decodeML : Coupling → Fin 32` — **syndrome decoding** = argmin Hamming distance = ground-state
    finder; `:74` `decodedCodeword`.
  - `:121` **`ml_decoder_capstone`** — bundles: parameters; **Hamming bound** `1+codeLength ≤ 2^(n−k)`
    (`:126`); clean reception `cocycleObstruction c₁=0`, `c₂=0` (`:130-131`, `s=0` ⟺ codeword); 1-bit
    error ground=1 at all 10 positions (`:133-146`); **decoder recovery** `decodedCodeword(flipBit c₁ e)=c₁`
    (`:148-150`, 1-error correction); **nonzero syndrome** under error `cocycleObstruction(flipBit c₁ e)=3`
    (`:152-154`, the `q=−1` escape); 2-bit error ground=2 (`:156-157`, beyond `d/2`). All `decide`.
- `Lib/Math/Cohomology/HodgeConjecture/Bridge/SpinGlass.lean` (**13/0 PURE**) — the parity-check / generator
  cochain complex:
  - `:79` `delta0 : Spin → Coupling` (= **generator `G`**, `δ₀ σ(e)=σ(src e)⊕σ(tgt e)`, codewords `=im δ₀`).
  - `:87` `delta1 : Coupling → TriCochain` (= **parity-check `H`**, `δ₁ J(t)=` XOR of J over triangle t's
    3 edges — each triangle = one parity-check row).
  - `:113` `cocycleObstruction : Coupling → Nat` (= the **syndrome** weight, `|δ₁ J|`).
  - `:134` `spin_glass_213_capstone` — `cocycleObstruction(δ₀ σ)=0` (`:136-139`, **`H·Gᵀ=0 = δ²=0`**),
    `J_oneAnti` syndrome `=3` (`:147`), nonzero-vs-zero discriminator (`:153-154`).
- `Lib/Math/Cohomology/Examples/NonzeroBetti.lean` (**56/0 PURE**) — minimum distance / syndrome `q=±1` tag:
  - `:111` `betti_one_cycle` (`im δ⁰ ⊊ ker δ¹`, a nonzero cocycle survives = **smallest nonzero codeword /
    min distance**).
  - `:134` `loopClass_not_coboundary`, `:143` `nonzero_cohomology_class` (a closed-not-exact cocycle =
    **nonzero syndrome class**, the `q=−1` escape).
  - `:173` `cycle_vs_contractible_qpm` (`multiplier escape=−1`, `converge=+1` = **`s≠0` vs `s=0` tag**).
- `Lib/Math/Cohomology/Infrastructure/BoolXORFold.lean` (**6/0 PURE**) — `:38` `psiNatPos_linear`
  (`Ψ(v⊕w)=Ψ(v)⊕Ψ(w)` = **syndrome/error linearity**, the 𝔽₂ character homomorphism); `:25` `xor_pair_swap`.
- `Lib/Physics/Symmetry/AutKGroup.lean` — `:82` `C2_6.mul` (the **𝔽₂ⁿ XOR group** = the code's ambient
  space, each element self-inverse); `:71-72` note: packed `Nat.xor` is DIRTY, pointwise `Bool.xor` PURE
  (the purity boundary on the syndrome map).
- `Lib/Math/NumberTheory/ModArith/Zolotarev.lean` — `:133` `psign_mulPerm_hom` (the {±1}-valued sibling of
  the syndrome character; `parity.md`'s arrow). Cited PURE across the corpus.
- `Lib/Math/Probability/Information/Coding.lean` (**10/0 PURE**) — the **Hamming metric** itself:
  `:27` `hammingDistance`, `:34` `hamming_self` (d(x,x)=0), `:50` `hamming_symm` (symmetry), `:63`
  `hamming_triangle_concrete` (triangle inequality, concrete), `:41` `hamming_swap` (concrete d=2). The
  metric `decodeML` minimizes; module docstring (`:15`) names "**linear code = subgroup of Bool^n under
  XOR**".
- `Lib/Math/Combinatorics/Mex.lean` (**12/0 PURE**) — `:124` `mex`, `:95` `mexFrom_finds` (the
  least-missing-value / bounded-diagonal engine; cross-frame to `game_theory.md`, the finite `q=−1`
  residue).
- cross-frame: `homology.md` (`ker δ/im δ` residue, `∂²=0`, `dsq_zero_universal_delta4`), `parity.md` /
  `game_theory.md` (the XOR/𝔽₂ character), `fourier.md` (character orthogonality).

Scan tallies this pass (`python3 tools/scan_axioms.py <module>` from repo root):
`MLDecoder` **13/0**, `SpinGlass` **13/0**, `NonzeroBetti` **56/0**, `Coding` **10/0**. (`BoolXORFold` 6/0,
`Mex` 12/0, `Zolotarev` PURE — per `game_theory.md`/corpus, not re-scanned this pass.)

### Dropped / flagged (could not verify or predicted-not-built)

- **No abstract `LinearCode` / `Code` type** with arbitrary `n,k` over 𝔽₂ or 𝔽_q (grep:
  `Hamming|syndrome|parityCheck|LinearCode|generator_matrix|minimum_distance` over `lean/` hits only the
  K₅-concrete `MLDecoder`/`SpinGlass`, the `Coding.lean` metric, and the Hodge-bridge primitives). The K₅
  `[10,4,4]` instance is the only built code; the parametric object is predicted-not-built.
- **Hamming codes** `[2^m−1, …, 3]` as a family, and the **general `n,k,d` Hamming/sphere-packing bound**
  (only the K₅ numeric instance `1+10 ≤ 2^6` is verified) — ABSENT.
- **Singleton bound `d ≤ n−k+1`** and a named **MDS** predicate — ABSENT (a rank–nullity / weight-count
  identity the calculus predicts; no theorem states it). Flagged predicted-not-built, NOT cited.
- **Reed–Solomon / BCH / LDPC** — named only as industry context (`MLDecoder.lean:104-108`); need 𝔽_q
  (`q>2`) + polynomial evaluation, the `q>2` analogue of `game_theory.md`'s 𝔽₂ ceiling. Not built.
- The **`∀`-quantified minimum-distance theorem** (`d` = min nonzero weight over *all* codewords) is
  verified only at concrete codewords (`MLDecoder.lean:36`; full enumeration is Rust-side). The abstract
  `∀`-statement is the same finite-`List` quantifier limit `measure.md`/`topology.md` locate. Flagged, not
  asserted.
- No buildable witness proposed: the central claims are already closed theorems
  (`ml_decoder_capstone`, `spin_glass_213_capstone`, `nonzero_cohomology_class`), so no new `decide`
  witness is offered (per the prompt's caution against proposing unverified inequalities).
