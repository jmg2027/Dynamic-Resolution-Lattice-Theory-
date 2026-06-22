# Decomposition: higher / Milnor K-theory (K₁ = GL/[GL,GL], K₂ and the Steinberg symbol {a,b}, Milnor K^M_*(F), the norm-residue / Milnor conjecture, Quillen's higher K_n)

*A FRESH decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants — the
`×↦·`/`×↦+` character arrow and the `q=±1` residue tag — plus the spine). This sits **one degree above**
`k_theory.md` (KEY — K₀ = the group-completion difference-Lens; do not duplicate: that note built
degree 0, the EXACT/`q=+1` part) and fuses `determinant.md`/`groups.md` (K₁ = det = abelianization =
the commutator-quotient), `galois_cohomology.md` (KEY — the Milnor conjecture: K^M/2 ≅ Galois
cohomology), `quadratic_forms.md` (JUST DONE — Milnor K-theory ≅ the graded Witt ring), and
`quadratic_reciprocity.md` (the Hilbert/Steinberg symbol = the q=±1 reciprocity).*

**Thesis under test (NOT to re-skin):** higher K-theory is the calculus's **character arrow climbing the
degree, with the q=±1 Steinberg cut.**
- **K₁(R) = GL(R)/[GL,GL]** = the **abelianization** = the `det`/`×↦·` character (`determinant.md`):
  for a field K₁(F)=F*, `det` being THE map to the abelianization; the commutator quotient = **killing
  the q=−1 non-abelian part** (`groups.md`'s derived-series/commutator machinery — `commSet = [G,G]`,
  commutators are even-sign).
- **K₂ and the Steinberg symbol {a,b}** = the **q=±1 antisymmetric, bimultiplicative pairing**:
  `{a,b}{b,a}=1` is the SAME q=±1 swap/antisymmetry as the Lie bracket (`bracket_antisymm`) / the
  signed cup (`cup1_antisymmetric`), and `{a,b}` is bimultiplicative = the `×↦·` character **in each
  slot**.
- **Milnor K-theory K^M_*(F)** = the **tensor algebra of F\* mod the Steinberg relation {a,1−a}=0** —
  the `×↦·` character **tensored up, graded**, with `{a,1−a}=0` the defining q=±1 cut (a
  graded-relation slot, `../SYNTHESIS.md` §5 item 3).
- **The Milnor conjecture / norm residue** (`K^M_n(F)/2 ≅ H^n(F,ℤ/2)` Galois cohomology, AND ≅ the
  graded Witt ring `grW`) = the **deepest tie**: `galois_cohomology.md` + `quadratic_forms.md` +
  K-theory are **ONE graded object** read three ways.

**NO new primitive.** Higher K-theory = (K₁ = the `det`/`×↦·` character = abelianization,
commutator-quotient killing q−1) + (K₂/symbol = the q=±1 antisymmetric bimultiplicative pairing,
Steinberg) + (Milnor K = the `×↦·` character graded mod Steinberg) + (Milnor conjecture = K^M/2 ≅
Galois cohomology ≅ graded Witt, one object). The named `K1`/`K2`/`MilnorK`/`Steinberg`/`KTheory`
objects are **predicted-ABSENT — grep-confirmed below** (zero declarations).

---

## The decomposition (C / Reading / Residue)

- **Construction `C` — the multiplicative group F\* (and GL), nothing new.** For a field, the carrier of
  higher K-theory is the **unit group F\*** — `exponential.md`/`prime_factorization.md`'s ×-construction
  (the distinguishable ×-atoms), here read as a group. For a ring it is `GL(R) = lim GL_n(R)`, the
  `groups.md` `Aut`-family of the free module (a composition-closed family of `C`-preserving
  self-readings, `PermGroup`/`composeList`). The fold-height axis is the **degree `n`** (K₁, K₂, …,
  K^M_n); the direction/swap-bit is the **q=±1 antisymmetry** of the symbol. No field-theoretic
  primitive: `C` is the unit-group / `GL` the calculus already has.

- **Reading `L` — the abelianization character (K₁), then the graded antisymmetric symbol (K₂/K^M).**
  - **K₁ = the abelianization reading.** `K₁(R) = GL/[GL,GL]` = `GL` read by **"quotient by the
    commutator"** = the universal map to an abelian group = the `×↦·` character. For a field, `K₁(F)=F*`
    and the realized character is **`det`** (`det(MN)=det M·det N`, `det2_mul`): `det : GL → F*` IS the
    map to the abelianization, and `[GL,GL] = SL` (det 1) is its kernel. The commutator-quotient =
    **killing the q=−1 non-abelian part** (`groups.md`'s `commSet g h = g⁻¹h⁻¹gh`; commutators land in
    the even-sign / det-1 part, `gcommP_transpositions_even`/`three_cycle_commutator_S5_even`:
    `psign(gcomm)=1`).
  - **K₂ / Steinberg symbol = the antisymmetric bimultiplicative pairing.** `{a,b} ∈ K₂(F)` is
    `×↦·`-linear in *each* slot (`{aa',b}={a,b}{a',b}`) and **antisymmetric** (`{a,b}{b,a}=1`,
    i.e. `{a,b}=−{b,a}` additively) — the q=±1 swap-bit on a two-slot reading, the SAME antisymmetry as
    the Lie bracket `[A,B]=−[B,A]` (`bracket_antisymm`) and the signed cup `eᵢ∧eⱼ=−(eⱼ∧eᵢ)`
    (`cup1_antisymmetric`).
  - **Milnor K^M_n = the `×↦·` character tensored up, mod Steinberg.** `K^M_*(F) = T(F*)/⟨a⊗(1−a)⟩` —
    the tensor algebra of F\* (the `×↦·` character iterated, graded by `n`) modulo the **Steinberg
    relation `{a,1−a}=0`** (a graded-relation slot, `../SYNTHESIS.md` §5: a fixed linear law among a
    family of products under one reading, the same shape as the cup-Leibniz/skein relation).

- **Residue, tagged q=±1.**
  - **`q=+1` (the abelian/exact part).** K₁'s abelianization is the converging/closure pole: the
    universal abelian quotient *exists* and *closes* (`clo_idempotent`; the `det` character captures the
    multiplicative content). `det=1` (`[GL,GL]=SL`) is the flat/conserved q=+1 corner
    (`det_holonomy_eq_one` — the same multiplicative-flatness Noether-invariant as `noether.md`).
  - **`q=−1` (the antisymmetric / obstruction residue).** The **non-abelian commutator part** killed by
    K₁ is the q=−1 residue (the quintic's pole, `a5_perfect`: `[A₅,A₅]=A₅` — a *perfect* group whose
    abelianization is trivial because the whole group IS its commutator, the extreme q=−1 escape,
    `perfect_nontrivial_not_solvable`). The **antisymmetry of {a,b}** is the q=−1 swap-bit; the
    Steinberg relation `{a,1−a}=0` is the q=±1 cut that defines the graded ring. Higher K_n (n≥2) are
    the graded q=−1 obstruction residue, exactly `k_theory.md`'s "higher K_n = the Ext^{>0} analogue".

---

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   F* / GL(R)                  =  ⟨ the unit-group / Aut-family ×-construction | — ⟩        (C; groups.md, PermGroup)
   K₁(R) = GL/[GL,GL]          =  the ABELIANIZATION reading  =  the ×↦· character          (det = the map to the abelianization)
       K₁(F) = F*  (field)     =  det : GL → F*, kernel [GL,GL]=SL (det 1)                   (det2_mul; det=1 = q+1 flat)
       [GL,GL]  (commutator)   =  the q=−1 non-abelian part KILLED by the quotient          (commSet=[G,G]; gcomm even-sign)
   K₂(F) ∋ {a,b} (Steinberg)   =  the q=±1 ANTISYMMETRIC bimultiplicative pairing
       {a,b}{a',b}={aa',b}     =  the ×↦· character IN EACH SLOT                            (det2_mul/legendre_mul, two slots)
       {a,b}{b,a}=1            =  q=−1 antisymmetry (swap-bit)  =  [A,B]=−[B,A] = eᵢ∧eⱼ=−(eⱼ∧eᵢ)  (bracket_antisymm, cup1_antisymmetric)
   K^M_*(F) = T(F*)/⟨a⊗(1−a)⟩  =  the ×↦· character TENSORED UP, graded by n, mod the Steinberg cut
       {a,1−a}=0  (Steinberg)  =  the defining q=±1 graded-relation cut                     (graded-relation slot, SYNTHESIS §5; leibniz_universal_delta4 shape)
   K^M_n(F)/2 ≅ H^n(F,ℤ/2)     =  the NORM-RESIDUE iso (Milnor conj.): K-theory = Galois cohomology  (galois_cohomology.md, ONE graded object)
   K^M_*(F)/2 ≅ grW(F)         =  ≅ the graded Witt ring                                    (quadratic_forms.md, the SAME object)
   {a,b}_p  (Hilbert symbol)   =  quadratic_reciprocity's local symbol, the q=±1 reciprocity (psign_mulPerm_hom; order-2 ×↦{±1})
   higher K_n (Quillen, n≥2)   =  the q=−1 graded obstruction residue  =  k_theory's Ext^{>0} analogue
```

So **K₁, K₂, the Steinberg symbol, Milnor K-theory, and the norm-residue isomorphism are ONE object**:
the `×↦·` character climbing the degree, with the q=±1 Steinberg/antisymmetry cut. K₀ (`k_theory.md`)
was the additive `×↦+` character at degree 0 (the difference-Lens group-completion, the q=+1 exact
part); higher K is the **multiplicative `×↦·` character at degree ≥ 1** with the q=±1 cut switched on.

## Re-seeing table (the unification)

| classical higher-K object | the calculus's reading | already in note | repo status / Lean anchor |
|---|---|---|---|
| K₁(R) = GL/[GL,GL] (abelianization) | the `×↦·` character = the abelianization quotient | `determinant.md`, `groups.md` | engine BUILT (`det2_mul`; `commSet`=`[G,G]`); named `K1` ABSENT |
| K₁(F) = F\* (field), det the map | `det : GL → F*` = the universal abelian character; [GL,GL]=SL | `determinant.md` | `det2_mul` (PURE); `det=1` flat = `det_holonomy_eq_one` |
| [GL,GL] (commutator subgroup) | the q=−1 non-abelian part KILLED by K₁ | `groups.md` (derived series) | `commSet`/`gcommP`, `gcommP_transpositions_even` (PURE) |
| K₂(F) Steinberg symbol {a,b} | the q=±1 antisymmetric bimultiplicative pairing | this note (NEW) | antisymmetry: `bracket_antisymm`, `cup1_antisymmetric` (PURE); named `K2`/`Steinberg` ABSENT |
| bimultiplicativity {aa',b}={a,b}{a',b} | the `×↦·` character in each slot | `determinant.md` | `det2_mul`, `legendre_mul` (PURE) |
| Milnor K^M_*(F)=T(F\*)/⟨a⊗(1−a)⟩ | the `×↦·` character tensored up, graded, mod Steinberg | `prime_factorization.md`, `quadratic_forms.md` | graded-relation slot (`leibniz_universal_delta4` shape); named `MilnorK` ABSENT |
| Steinberg relation {a,1−a}=0 | the defining q=±1 graded-relation cut | `../SYNTHESIS.md` §5 | partially grounded (`leibniz_universal_delta4`, the Leibniz/three-term shape) |
| Milnor conj. K^M/2 ≅ H^n(F,ℤ/2) | the norm-residue iso: K-theory = Galois cohomology, ONE object | `galois_cohomology.md` | residue-mechanism PURE; named iso ABSENT |
| K^M/2 ≅ graded Witt ring grW | the SAME object, signature side | `quadratic_forms.md` | signature instances BUILT; `WittRing` ABSENT |
| Hilbert symbol {a,b}_p | `quadratic_reciprocity`'s local symbol, q=±1 reciprocity | `quadratic_reciprocity.md` | `psign_mulPerm_hom` (order-2 `×↦{±1}`, PURE); named `Hilbert_symbol` ABSENT |
| Quillen higher K_n | the q=−1 graded obstruction residue (Ext^{>0} analogue) | `k_theory.md`, `homological_algebra.md` | `ResidueTag`/`escape_residue_outside` (PURE); named `K_n` ABSENT |

---

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse — K₁ is the `det`/`×↦·` character read as the abelianization; K₂/Milnor is the q=±1
antisymmetric symbol; the Milnor conjecture fuses three notes into ONE object.** Three previously-separate
fields are one graded reading:

1. **K₁ = the abelianization = `det` = the `×↦·` character (collapse with `determinant.md`/`groups.md`).**
   `GL/[GL,GL]` is, term-for-term, the universal map to an abelian group — which the calculus already
   names the **`×↦·` character** (`det(MN)=det M·det N`, `det2_mul`). For a field, `det : GL(F) → F*` is
   that map, `K₁(F)=F*`, and `[GL,GL]=SL` (the `det=1` kernel). The commutator-quotient is the calculus's
   q=−1/q=+1 split made literal: `[G,G]` (the commutator subgroup, `groups.md`'s `commSet g h =
   g⁻¹h⁻¹gh`) is the **q=−1 non-abelian part**, and commutators are forced into the even-sign / det-1
   corner (`gcommP_transpositions_even`: `psign(gcomm)=1`) — i.e. the abelianization *kills exactly the
   antisymmetric q=−1 residue* and keeps the q=+1 `det` character. The extreme case is the perfect group
   `[A₅,A₅]=A₅` (`a5_perfect`): abelianization trivial because the whole group is q=−1 commutator —
   `perfect_nontrivial_not_solvable`, the quintic's pole. **K₁ is not a new object; it is the `×↦·`
   character read as a quotient, the q=−1 commutator the part it discards.**

2. **K₂ / the Steinberg symbol = the q=±1 antisymmetric bimultiplicative pairing (the NEW datum).**
   `{a,b}` is `×↦·`-linear in each slot (the character, twice over) AND antisymmetric `{a,b}{b,a}=1`.
   The antisymmetry is **not a new structure**: it is the SAME q=−1 swap-bit the calculus has across the
   board — the Lie bracket `[A,B]=−[B,A]` (`bracket_antisymm`), the signed cup `eᵢ∧eⱼ=−(eⱼ∧eᵢ)`
   (`cup1_antisymmetric`), the determinant's sign, `∂²=0`'s orientation cancellation. So `{a,b}` =
   (the `×↦·` character) ⊗ (the q=−1 antisymmetry) — two already-built invariants combined, no third.
   The Steinberg *relation* `{a,1−a}=0` is the q=±1 **graded-relation cut** (`../SYNTHESIS.md` §5 item 3:
   a fixed linear law among a family under one reading), partially grounded by the cup-Leibniz three-term
   law `leibniz_universal_delta4` (the same shape as the skein/Steinberg relation).

3. **Milnor K^M_* = the `×↦·` character tensored up; the Milnor conjecture = ONE graded object across
   three notes (the deepest collapse).** `K^M_*(F) = T(F*)/⟨a⊗(1−a)⟩` is the multiplicative character
   *graded*, the tensor power iterated by the fold-height `n` and cut by Steinberg. The norm-residue
   isomorphism `K^M_n(F)/2 ≅ H^n(F,ℤ/2)` says the K-theory graded ring and **`galois_cohomology.md`'s**
   `H^n(G,ℤ/2)` (the residue-taking operation on the Galois invariants) are the **same graded object**;
   and `K^M_*(F)/2 ≅ grW(F)` says it is also **`quadratic_forms.md`'s** graded Witt ring (the q=±1
   signature counted, mod the hyperbolic q+1⊕q−1 neutral). So three notes that decomposed three fields
   independently — Milnor K, Galois cohomology, the Witt ring — are decomposing **ONE** graded object,
   exactly the calculus's two invariants graded by degree: the `×↦·` character (each slot of the symbol /
   each Witt class) with the q=±1 tag (the Steinberg cut / the disc-sign / the Ext^{>0} obstruction).
   This is the sharpest "different fields, one (C,L)" collapse the cluster has hit on the multiplicative
   side.

**Forcing.** (i) K₁ is *forced* to be the abelianization: the universal map to an abelian group is unique
(the same universal-property forcing as the group completion `lift_unique`), and `det` realizes it for a
field — not a chosen invariant. (ii) The symbol's antisymmetry is *forced* by the same q=−1 swap-bit that
forces `[A,B]=−[B,A]` and `eᵢ∧eⱼ=−(eⱼ∧eᵢ)` — a two-slot reading of a `C` carrying the direction bit *must*
read out antisymmetric (`bracket_antisymm`/`cup1_antisymmetric` are `decide`-proved, not posited).
(iii) The bimultiplicativity is *forced* to be the `×↦·` character (`det2_mul`/`legendre_mul` are pure ℤ
identities), so the symbol's two slots are the one arrow read twice.

**The q=±1 spine (`../SYNTHESIS.md` §3).** K₁'s abelianization = the q=+1 converge/closure pole (the
abelian quotient closes, `det` captures it, `det=1` flat); the killed commutator = q=−1 escape
(`[A₅,A₅]=A₅`, `escape_residue_outside`). K₂'s symbol antisymmetry = the q=−1 swap-bit; the Steinberg
cut `{a,1−a}=0` = the q=±1 relation that grades the ring. Higher K_n = the graded q=−1 obstruction
residue (the same spine as `k_theory.md`'s K₀-exact / higher-K-obstruction split, now read on the
*multiplicative* `×↦·` character rather than the additive `×↦+` rank).

So higher K-theory = (K₁ = `det`/`×↦·` = abelianization, commutator-quotient killing q−1) + (K₂/symbol =
the q=±1 antisymmetric bimultiplicative pairing, Steinberg) + (Milnor K = the `×↦·` character graded mod
Steinberg) + (Milnor conjecture = K^M/2 ≅ Galois cohomology ≅ graded Witt, one object) — **no new
primitive**.

---

## VALIDATE verdict — **EXTEND** (deep consolidation: K₁ = the abelianization character, K₂/Milnor = the q=±1 antisymmetric symbol; the Milnor conjecture = a THREE-NOTE fusion; named objects ABSENT)

No new primitive, no interior break. Higher K-theory slots into v7.1: `C` = the unit-group / `GL`
×-construction (direction/q=±1 + fold-height carried), `L` = the abelianization character (K₁) then the
graded antisymmetric symbol (K₂/K^M), `Residue` = the killed commutator / higher K_n, tagged q=±1. It is
a **decisive consolidation on the multiplicative side**, dual to `k_theory.md`'s additive K₀:

- K₀ = the **additive** `×↦+` character (rank/dimension) at degree 0, the difference-Lens group-
  completion, the q=+1 EXACT part (`k_theory.md`).
- K₁/K₂/Milnor = the **multiplicative** `×↦·` character at degree ≥ 1, with the q=±1 antisymmetry/Steinberg
  cut switched on — the two `×↦·`-vs-`×↦+` directions of the one character arrow, split across the two
  ends of the K-theory grading.

**PREDICTION legs (engine built, named object absent):**
- **K₁ = abelianization = the `×↦·` character.** Grounded: `det2_mul` (the character, PURE) and the
  commutator machinery `commSet=[G,G]` / `gcommP` with commutators forced even-sign
  (`gcommP_transpositions_even`, PURE), the abelianization-kills-q−1 content. The named `K1 = GL/[GL,GL]`
  object (a `GL_n` colimit, the `SL=[GL,GL]` kernel theorem) is the open leg — the same shape as
  `k_theory.md`'s absent K₀ object: engine built, the named graded object not assembled.
- **K₂ / Steinberg symbol = the q=±1 antisymmetric bimultiplicative pairing.** Grounded: the antisymmetry
  (`bracket_antisymm`, `cup1_antisymmetric`, both PURE) and the bimultiplicative `×↦·` character
  (`det2_mul`/`legendre_mul`, PURE). The named `Steinberg`/`K2` symbol object and the `{a,1−a}=0` relation
  on F\* are absent.
- **Milnor conjecture = ONE graded object (K^M/2 ≅ Galois cohomology ≅ grW).** Grounded at the residue-
  mechanism / grading-tag level across the three neighbor notes (`galois_cohomology.md`'s `ker δ/im δ` +
  `ResidueTag`; `quadratic_forms.md`'s signature instances; this note's `×↦·` symbol). The named
  norm-residue isomorphism object is absent — the deepest open leg, the abelian-category twin spanning
  three missing named objects at once.

**Located break (the `k_theory.md`/`galois_cohomology.md`/`quadratic_forms.md` spirit) — every named
higher-K object is ABSENT.** Grep over `lean/E213` for
`Milnor`/`Steinberg`/`KTheory`/`K_theory`/`MilnorK`/`K1`/`K2`/`norm_residue`/`Hilbert_symbol` returns
**zero K-theory declarations** (details in Dropped/flagged). The named objects (`GL`-colimit K₁, the
Steinberg symbol K₂, the Milnor tensor-algebra-mod-Steinberg, the norm-residue iso) are predicted-not-
built — the same located shape as the absent K₀, Ext^n, and WittRing objects across the cluster: the
*engines* (the character arrow, the antisymmetry swap-bit, the commutator/abelianization machinery, the
q=±1 tag, the group-completion) are each built and PURE; only the named graded K-theory objects that would
weld them are open.

---

## Verified Lean anchors (file:line:theorem) — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session

**K₁ = the `×↦·` character (det) = the abelianization; the commutator-quotient killing q−1:**
- `lean/E213/Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`
  (`det2(mul M N) = det2 M * det2 N` — the `×↦·` character; `det : GL → F*` = the map to the
  abelianization, K₁(F)=F*). **PURE, scanned 130/0.**
- `lean/E213/Lib/Math/Algebra/Linalg213/DerivedSeries.lean:91` `gcommP` (the group commutator
  `g⁻¹h⁻¹gh` on permutation lists); `:124` `commSet` (`= [G,G]`, the commutator subgroup — the
  abelianization's kernel); `:99` `commutator_nontrivial`; `:103` `gcommP_transpositions_even`
  (`psign(gcommP …)=1` — commutators land in the even-sign / det-1 q=+1 part); `:135` `derived_S3_step1`
  (`commSet S3 = A3`); `:144` `solvable_S3`. **PURE, scanned 21/0.**
- `lean/E213/Lib/Math/Algebra/Icosahedral/A5Perfect.lean:137` `a5_perfect` (`[A₅,A₅]=A₅` — the perfect
  group whose abelianization is trivial = the extreme q=−1 commutator pole); `:149` `a5_not_solvable`;
  `:64` `A5_card` (60). **PURE, scanned 9/0.**
- `lean/E213/Lib/Math/Algebra/Linalg213/Solvable.lean:237` `perfect_nontrivial_not_solvable`
  (the q=−1 escape: abelianization trivial because G IS its commutator); `:196` `isPerfect`,
  `:190` `isSolvable`; `solvability_two_poles`, `tagOfVerdict_A5`/`tagOfVerdict_S3` (the q=±1 tag on
  the abelianization tower). **PURE, scanned 65/0.**

**K₂ / Steinberg symbol = the q=±1 ANTISYMMETRIC bimultiplicative pairing:**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76` `bracket_antisymm`
  (`[A,B]=−[B,A]` — the q=−1 pair-swap, the SAME antisymmetry as `{a,b}{b,a}=1`). **PURE, scanned 10/0.**
- `lean/E213/Lib/Math/Cohomology/Cup/SignedCup.lean:62` `cup1_antisymmetric` (`eᵢ∧eⱼ=−(eⱼ∧eᵢ)`,
  `eᵢ∧eᵢ=0` — the orientation/antisymmetry sign the Steinberg symbol carries). **PURE, scanned 14/0.**
- bimultiplicativity (the `×↦·` character in each slot): `det2_mul` (above) +
  `lean/E213/Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul`
  (the order-2 `×↦{±1}` character). **PURE, scanned 5/0.**

**The Hilbert symbol {a,b}_p = quadratic_reciprocity's local symbol (q=±1 reciprocity):**
- `lean/E213/Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133` `psign_mulPerm_hom` (the sign is
  multiplicative — the order-2 `×↦{±1}` reciprocity character, per `quadratic_reciprocity.md`);
  `:142` `psign_mulPerm_qr`. **PURE, scanned 11/0.**

**The Steinberg relation {a,1−a}=0 = the q=±1 graded-relation cut (shape grounded by cup-Leibniz):**
- `lean/E213/Lib/Math/Cohomology/Delta/V4Capstone.lean:62` `leibniz_universal_delta4` (the cup-product
  Leibniz three-term law `δ(α⌣β)=δα⌣β ⊕ α⌣δβ` — the same graded-relation shape as the
  skein/Steinberg relation, `../SYNTHESIS.md` §5); `:41` `dsq_zero_universal_delta4` (the q=±1
  orientation-cancellation). (per `homology.md`/`two_cells.md`, PURE.)

**Higher K_n = the q=−1 graded obstruction residue (the Ext^{>0} analogue, k_theory.md):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:133`
  `escape_residue_outside` (q=−1 = higher K_n obstruction); `:160` `converge_residue_fixed` (q=+1 = K₁
  abelianization closes); `:86` `multiplier_unimodular` (the ±1 bit); `:180` `golden_is_converge`.
  **PURE, scanned 55/0.**

**The q=+1 flat/conserved corner (det=1 = [GL,GL]=SL = Noether-invariant):**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136`
  `det_holonomy_eq_one` (product of det-1 steps around a loop = 1 — the q=+1 multiplicative flatness,
  the K₁ kernel `SL` corner; `noether.md`). **PURE, scanned 26/0.**

**The carrier-polymorphic group-completion (K₀ engine, cross-ref to k_theory.md; degree-0 contrast):**
- `lean/E213/Lens/Number/Nat213/Tower/PairCompletionUniversal.lean:215`
  `invert_is_the_universal_group_completion`, `:169` `lift_unique` (the universal-property forcing K₁'s
  abelianization mirrors — same "unique map to an abelian object" engine). **PURE, scanned 19/0.**

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`SternBrocotMarkov` 130/0 · `DerivedSeries` 21/0 · `A5Perfect` 9/0 · `Solvable` 65/0 · `Mat2Bracket`
10/0 · `SignedCup` 14/0 · `LegendreMultiplicative` 5/0 · `Zolotarev` 11/0 · `ResidueTag` 55/0 ·
`HolonomyLattice` 26/0 · `PairCompletionUniversal` 19/0 · `PrimeValuation` 7/0. **All PURE.**
(`leibniz_universal_delta4`/`dsq_zero_universal_delta4` cited from `V4Capstone`, PURE per
`homology.md`/`two_cells.md`.)

## Dropped / flagged (honest)

- **`Milnor` / `Steinberg` / `KTheory` / `K_theory` / `MilnorK` / `norm_residue` / `Hilbert_symbol`
  OBJECTS — ABSENT, grep-confirmed.** Grep over `lean/E213` for
  `Milnor|Steinberg|K_theory|KTheory|MilnorK|norm_residue|Hilbert_symbol` returns **zero declarations**.
  (The five `Milnor` file-matches — `DyadicCompletion.lean`, `ARCHITECTURE.md`, `Term.lean`,
  `Term/API.lean`, `Space.lean` — are unrelated: Milnor-exponent/Milnor-attractor narrative in dynamics
  and the Space module, NOT Milnor K-theory; `Steinberg`/`KTheory`/`norm_residue`/`Hilbert_symbol` have
  no matches at all.) There is **no** `K1 = GL/[GL,GL]` object, **no** `K2`/Steinberg symbol, **no**
  Milnor tensor-algebra-mod-Steinberg, **no** norm-residue isomorphism. Predicted-not-built, confirmed.
- **`K1`/`K2` as named K-groups — ABSENT.** The `K1`/`K2` grep is dominated by unrelated
  identifiers (decode/coding `K1`, etc.); no algebraic-K-theory K-group object exists. Cited as absent.
- **The `symbol` grep hits are unrelated** — modular symbols (`MinkowskiModularSymbol`,
  `PeriodReciprocity`), the Bollobás set-pair (`BollobasSetPair`), discrete-log/Legendre symbols
  (`DiscreteLogParity`, `DyadicFSM/Legendre`), and the Shannon/coding "symbol" (Information cluster) —
  NOT the Steinberg/Hilbert symbol. Not cited as a higher-K anchor.
- **The Steinberg relation `{a,1−a}=0` as a Lean relation on F\* — ABSENT.** The graded-relation *shape*
  is grounded (`leibniz_universal_delta4`, the cup-Leibniz three-term law); the specific
  `a⊗(1−a)` Steinberg cut on the unit group is not built (it lives in the same graded-relation slot
  `../SYNTHESIS.md` §5 named partially grounded).
- **The Milnor conjecture / norm-residue isomorphism as a theorem — ABSENT, identified not asserted.**
  The note's claim is an *identification* (K^M/2 ≅ Galois cohomology ≅ grW = one graded object), grounded
  by the three neighbor notes' residue-mechanism / signature / character anchors; there is no
  `norm_residue`/`MilnorConjecture` Lean object. The deepest open leg — three missing named objects fused.
- **`GL`/`SL` colimit and `[GL,GL]=SL` theorem — ABSENT.** The commutator/abelianization machinery is
  built for finite permutation groups (`commSet`/`gcommP` on `S₃`/`A₅`), not for `GL_n(R)` with the
  `[GL,GL]=SL` (Whitehead) theorem. The finite-group instances ground "abelianization kills the q−1
  commutator"; the `GL`-specific named K₁ object is the open leg.
- **Verified buildable witness.** A small ∅-axiom witness the calculus predicts (the abelian-quotient
  analogue of `k_theory.md`'s named-K₀ target): instantiate the **abelianization-kills-commutator** content
  on a concrete finite group as a `K1`-toy — e.g. `K1(S₃) := S₃ / commSet S₃ ≅ C₂` is already a
  `decide`/`rfl` corollary of `derived_S3_step1` (`commSet S3 = A3`, so the abelianization is `S₃/A₃ ≅
  C₂` = the `det`/sign character `psign`), naming `K1_of_S3 := …` and recording `K1_of_S3 ≅ C₂` via
  `psign`. For the antisymmetric symbol: a two-slot `decide`-checkable `steinbergSymbol` toy on a small
  finite multiplicative group exhibiting bimultiplicativity (`det2_mul`-style) + antisymmetry
  (`bracket_antisymm`/`cup1_antisymmetric`-style) — welding the (all-built) character + swap-bit
  invariants into a named symbol on a finite carrier, the higher-K analogue of `NonzeroBetti.lean`'s
  named cohomology class. The general `GL_n(R)`/`F*` carrier and the norm-residue iso remain the open
  named-object legs. (Not asserted closed here — every cited fact above is a grep-confirmed,
  scanned-PURE existing theorem.)
