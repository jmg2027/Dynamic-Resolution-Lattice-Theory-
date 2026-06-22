# Decomposition: algebraic K-theory at K₀ (the Grothendieck group)

*A FRESH decomposition per `../README.md` (model v7.1). The high-leverage thesis to **test**, not
re-skin: **K₀ is `integers.md`'s group-completion = the difference-Lens, run one level up — applied to a
monoid of objects instead of to ℕ.** `integers.md` established ℤ = the difference-Lens on directed
count-pairs `(m,n) ↦ m − n` (`difference_lens_founds_on_count`, `06_lens_readings.md §6.7`). K₀ is the
SAME construction with "iso-class of object" replacing "unit count": the Grothendieck group of
`(iso-classes, ⊕)` is the formal differences `[A] − [B]`, i.e. the directed pair `([A],[B])` read by the
difference-Lens. The rank/dimension map K₀ → ℤ is the additive character `×↦+` (`vp_mul`-style: `⊕ ↦ +`);
the short-exact relation `[B] = [A] + [C]` is the additive character read on the `homological_algebra.md`
residue machine — the `q=+1` exact part (`Ext⁰`, residue empty). So K-theory's K₀ = (the difference-Lens
of `integers.md`) ⊕ (the additive character) ⊕ (the exact-sequence `q=+1` part) — no new primitive, with a
genuinely NEW datum (below): the SAME `Quot`-free group-completion theorem the repo built for ℤ is
parametrized over an **arbitrary `CommCancelSemigroup`**, so the lift to a monoid of objects is verbatim,
not analogy. The deeper residue (higher `K_n`, the `q=−1` escape) is the obstruction analogous to
`Ext^{>0}`.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **directed pair of objects** `([A], [B])`, where each entry is an iso-class
  of objects of an additive/exact category `C`, with the commutative monoid operation `⊕` (direct sum,
  `[A] ⊕ [A'] = [A ⊕ A']`). This is `integers.md`'s **directed count-pair `(m, n)` with `[A]` replacing
  the count `m`**: the count `m` was itself iterated distinguishing read by `Lens.leaves` (`⟨1,1,+⟩`);
  here the entry is a richer object but `C` is the *same shape* — two entries of a commutative cancellative
  monoid, distinguished with a direction (which is the minuend). The "direction" bit is exactly
  `integers.md`'s swap-bit: `([A],[B])` vs `([B],[A])` is the sign of the formal difference. **No new
  primitive over `integers.md`'s pair construction** — only the monoid carrier is enriched from `(ℕ,+)` to
  `(iso-classes, ⊕)`.

- **Reading `L₋`** — the **difference-Lens**, verbatim from `integers.md`: `([A],[B]) ↦ [A] − [B]`, the
  formal difference. In Lean exactly the repo's group-completion `lift`: `lift f (a,b) = f a − f b`
  (`PairCompletionUniversal.lift`). K₀ is the *readout* of this Lens on the object-monoid, magnitude the
  monoid-element, sign the pair-swap. The **rank / dimension map** `K₀ → ℤ` is then `L₋` post-composed with
  the **additive character** `×↦+`: `dim(A ⊕ B) = dim A + dim B` is the `⊕ ↦ +` arrow, the *same* arrow as
  `vp(a·b) = vp a + vp b` (`PrimeValuation.vp_mul`) — `dimension.md`'s `L↑` height-reading, here the
  universal additive invariant.

- **Residue `q = ±1`** —
  - **`q = +1` (the exact part — the relation that closes).** The short-exact `0 → A → B → C → 0`
    forces `[B] = [A] + [C]` (not just `[A ⊕ C]`): the relation a K₀-character must respect. This is the
    `q=+1` exact pole of the `homological_algebra.md` machine — `Ext⁰ = Hom`, residue empty, `ker = im`
    (`reduced_betti_d4_contractible`): the additive invariant *captures* the extension, no obstruction.
    Group completion's own quotient (`[A]+[C]` vs `[A⊕C]` vs the split) is the converging/closure pole
    (`clo_idempotent`, `converge_residue_fixed`).
  - **`q = −1` (the obstruction — higher `K_n`).** `K₀` is the **degree-0 / exact part** of a graded
    family; `K_1`, `K_2`, … are the `q=−1` obstruction residue — automorphisms-mod-elementary,
    Steinberg/Milnor relations, the part the additive (rank) character *cannot* capture, exactly analogous
    to `Ext^{>0}/Tor_{>0}` (`escape_residue_outside`, `object1_not_surjective`). And `L₋` itself is
    many-to-one (the whole "translation" anti-diagonal `([A]⊕[D],[B]⊕[D])` reads the same difference —
    `npairToInt_translation_invariant` one level up), the per-reading residue `integers.md` already named.

## Re-seeing — ⟨C | L⟩

```
   K₀(C)                       =  ⟨ directed object-pair ([A],[B]) over (iso-classes, ⊕) | L₋ = [A] − [B] ⟩
                                  = integers.md's ℤ-construction, "object" replacing "unit count"
   "[A] − [B]"  (formal diff)  =  L₋ of any pair with that difference   (= lift f (a,b) = f a − f b)
   the sign of a K₀-class      =  the pair-swap bit of C  (([A],[B]) vs ([B],[A]))  — integers.md's sign
   rank / dimension  K₀ → ℤ    =  L₋ then the additive character ×↦+  (⊕ ↦ +, the vp_mul/det2_mul arrow)
   "[A⊕A'] = [A] + [A']"       =  the additive character on ⊕         (universal additive invariant)
   "[B] = [A] + [C]" (0→A→B→C→0) =  the q=+1 EXACT part (Ext⁰, residue empty: ker=im, the relation closes)
   K₀ is universal             =  group-completion universal property (invert_is_the_universal_group_completion)
   higher K_n (K₁, K₂, …)      =  the q=−1 obstruction residue  =  homological_algebra's Ext^{>0} analogue
```

So **the Grothendieck group, the formal difference, the rank character, and the short-exact relation are
ONE construction** — `integers.md`'s group-completion difference-Lens, with the monoid carrier enriched
from `(ℕ,+)` to `(iso-classes, ⊕)` and the exactness relation read on the `homological_algebra.md`
`q=+1` exact pole. Set against the notes it consolidates:

| classical K₀ object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| Grothendieck group `K₀(C)` | group-completion of `(iso-classes,⊕)` = difference-Lens one level up | `integers.md` (ℤ = the `(ℕ,+)` case) | `invert_is_the_universal_group_completion` |
| formal difference `[A]−[B]` | `L₋` = `lift f (a,b) = f a − f b` | `integers.md` (`diffView`, `npairToInt`) | `PairCompletionUniversal.lift`, `lift_combine` |
| `[A⊕A'] = [A]+[A']` (additive) | the additive character `×↦+` (`⊕↦+`) | `dimension.md` (`L↑`), `prime_factorization` | `PrimeValuation.vp_mul`, `det2_mul`, `legendre_mul` |
| K₀ universal (every additive inv. factors) | group-completion universal property (existence ∧ uniqueness) | `integers.md`, `galois.md`/`adjunction.md` (initiality) | `invert_is_the_universal_group_completion`, `lift_unique` |
| `[B]=[A]+[C]` (0→A→B→C→0 splits in K₀) | the `q=+1` exact part: `ker=im`, residue empty | `homological_algebra.md` (`Ext⁰`, exact) | `reduced_betti_d4_contractible` |
| higher `K_n` (K₁, K₂, …) | the `q=−1` obstruction residue (graded) | `homological_algebra.md` (`Ext^{>0}`) | `escape_residue_outside`, `ResidueTag` |
| the sign of `[A]−[B]` | the pair-swap direction bit of `C` | `integers.md` (sign = pair-swap) | `difference_lens_founds_on_count` (`= −(−·)`) |

## LEVERAGE — is K₀ literally `integers.md`'s group completion one level up?

**Verdict: EXTEND by consolidation — and the strongest "the construction lifts verbatim" datum in the
notebook after `integers.md`.** K₀ adds no new axis and no new primitive. The genuinely new datum is that
the repo's group-completion theorem is **already parametrized over an arbitrary commutative cancellative
monoid**, so "ℤ from ℕ" and "K₀ from (iso-classes, ⊕)" are *the same theorem at two carriers* — not an
analogy, a literal instantiation (modulo the absent object-monoid carrier, below). Leg by leg, honest.

**(1) ★ The group-completion machine is built `Quot`-free over an ARBITRARY `CommCancelSemigroup` — this
is the leverage.** `PairCompletionUniversal.invert_is_the_universal_group_completion` (PURE, scanned 19/0)
proves, for *every* abelian-group target `H` and *every* semigroup-hom `f : M → H`, that the difference
map `lift f (a,b) = f a − f b` is (i) well-defined on the completion (`lift_respects_pairEquiv`), (ii) a
homomorphism `lift(p∘q) = lift p + lift q` (`lift_combine`), (iii) factors `f` through `η`
(`lift_eta`), and (iv) is **unique** (`lift_unique`) — *choice-free*, since the only AC obstruction is
for `g`'s that aren't maps on the completion at all. This is the **complete group-completion universal
property** (initiality / left adjoint), and it is exactly what K₀ *is*: the universal additive invariant.
`integers.md`'s ℤ is the `M = (Nat213, +)` instance (`addCCS_completion_is_Int`: `liftZ (2,1) = +1`,
`liftZ (1,2) = −1`). K₀ is the same theorem with `M = (iso-classes, ⊕)`. The repo's own docstring states
this: `invert_is_one_move` is "the same construction at `+` (ℤ) and `·` (ℚ₊)" — K₀ is the *third* carrier
of the one move. So K₀'s universal property is not a new object to prove; it is `integers.md`'s theorem
read on a richer `M`. The file's docstring already calls `subNatNat_additive` "the Grothendieck/group law
of the difference-Lens" (`DifferenceLensFounding.lean:58`) — the field's name is *already in the repo*.

**(2) ★ The rank/dimension map = the additive character `×↦+`, the SAME arrow as `vp_mul`.** K₀'s
characters (rank, dimension, Euler characteristic) are additive: `dim(A ⊕ B) = dim A + dim B`. This is the
`⊕ ↦ +` instance of the calculus's single additive character — the *same* arrow proven multiplicative-to-
additive in `PrimeValuation.vp_mul` (`vp(a·b) = vp a + vp b`, PURE 7/0), `det2_mul`
(`SternBrocotMarkov.lean:104`), and `legendre_mul`. The README's `×↦+` column (parity / valuation /
entropy / Fourier / ζ) gains K₀'s rank as one more reading of the one arrow: the universal additive
invariant is, structurally, `dimension.md`'s height-reading `L↑` made a group homomorphism out of the
group completion. So "rank is the universal additive invariant on K₀" = "the `×↦+` character is the unique
arrow the group completion factors through" — the same statement as `lift`'s universal property (leg 1).

**(3) ★ The short-exact relation `[B]=[A]+[C]` = the `q=+1` exact part of the `homological_algebra.md`
machine.** What distinguishes K₀ from the bare monoid completion is the extra relation forced by
`0 → A → B → C → 0`: `[B] = [A] + [C]` (additivity *on extensions*, not just on `⊕`). In the calculus
this is precisely `homological_algebra.md`'s `q=+1` exact pole: an exact sequence is the residue-empty
case (`ker = im`, `reduced_betti_d4_contractible`, PURE 11/0) — `Ext⁰ = Hom`, the part that *closes*. So
"K₀ quotients by exact sequences" = "K₀ lives in the `q=+1` exact corner of the derived-functor machine":
the additive character captures the extension, no obstruction. A *split* extension (`[B]=[A⊕C]`) and an
exact one (`[B]=[A]+[C]`) agree in K₀ *because* K₀ is the `q=+1` corner — the converging/closure pole
(`clo_idempotent`, `converge_residue_fixed`). This is the same q=+1/q=−1 split `Ext¹` uses (split = q=+1,
no residue) read on K₀'s defining relation.

**(4) Higher `K_n` = the `q=−1` obstruction residue, graded — the `Ext^{>0}` analogue.** K₀ is the
*degree-0* / exact part of a graded family `K_n`. `K_1` (automorphisms mod elementary), `K_2` (Steinberg
relations), … are what the additive (rank) character *cannot* capture — the `q=−1` escape
(`escape_residue_outside`, `object1_not_surjective`), graded by `n`, exactly the `Ext^{>0}/Tor_{>0}` shape
of `homological_algebra.md`. K₀ sits at the `q=+1` pole (the universal additive invariant *exists*, the
group completion *closes*); the higher `K_n` are the `q=−1` residue the rank reading leaves. The
`ResidueTag` (`residue_tag_two_poles`, PURE 55/0) is the formal home: K₀ = converge (the invariant is
reached), higher `K_n` = escape (the obstruction surfaces). Conceptual at the named-`K_n`-object level
(absent, below); the *poles* are the built tag.

**Honest boundary — Lean-built vs conceptual/absent.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the **group-completion universal property** over
  an arbitrary `CommCancelSemigroup` — `invert_is_the_universal_group_completion`, `lift`, `lift_combine`,
  `lift_respects_pairEquiv`, `lift_eta`, `lift_unique`, `addCCS_completion_is_Int`
  (`PairCompletionUniversal.lean`, **19/0**), with `invert_is_one_move` (`PairCompletion.lean`, **17/0**);
  (b) the **difference-Lens founding** — `difference_lens_founds_on_count`, `subNatNat_additive` ("the
  Grothendieck/group law"), `difference_lens_slash_additive` (`DifferenceLensFounding.lean`, **4/0**),
  `npairToInt` + `npairToInt_translation_invariant` (`NatPairToInt.lean`); (c) the **additive character
  `×↦+`** — `vp_mul` (`PrimeValuation.lean`, **7/0**), `det2_mul` (`SternBrocotMarkov.lean:104`),
  `legendre_mul`; (d) the **`q=+1` exact part** — `reduced_betti_d4_contractible`
  (`BettiKernel.lean:63`, **11/0**); (e) the **`q=±1` tag** grading K₀ vs higher `K_n` —
  `residue_tag_two_poles`, `escape_residue_outside`, `converge_residue_fixed` (`ResidueTag.lean`,
  **55/0**); (f) the **closure/split pole** — `clo_idempotent` (`GaloisConnection.lean`).
- *Conceptual-only / the precise missing leg (the `homological_algebra.md`/`sheaf_theory.md`-style gap):*
  the **monoid-of-iso-classes carrier and the named K-theory objects are ABSENT.** Grep over `lean/E213`
  for `K0`/`GrothendieckGroup`/`KTheory`/`isoClass`/`AbelianCategory`/`ShortExact`/`DirectSum`/`exact_sequence`
  returns **zero Lean declarations** (the only `Grothendieck` hits are *docstrings* in
  `DifferenceLensFounding`/`PairCompletion*`/`SignedCut` naming the construction). There is **no**
  `(iso-classes, ⊕)` monoid object to instantiate `M` with, **no** named `K₀`/`K_n` object, **no**
  short-exact-sequence type (the K₀-defining relation lives only as the abstract `q=+1` exact condition,
  not as a relation imposed on a monoid of objects). This is the SAME shape as `homological_algebra.md`'s
  missing `Ext^n`/resolution object: the *group-completion engine* (`PairCompletionUniversal`, fully
  general over `M`), the *difference-Lens*, the *additive character*, the *`q=+1` exact part*, and the
  *`q=±1` grading* are each built and PURE; the **object-monoid carrier and the named `K₀(C)`/`K_n` that
  would weld them** are the located open legs.

So: **EXTEND by consolidation (K₀ = `integers.md`'s group-completion difference-Lens at the object-monoid
carrier; rank = the `×↦+` character; the short-exact relation = the `q=+1` exact part; higher `K_n` = the
`q=−1` obstruction residue), cashed at the universal-property / difference-Lens / character / exact-pole
level over an arbitrary `CommCancelSemigroup`; PARTIAL because the (iso-classes, ⊕) carrier and the named
`K₀`/`K_n`/short-exact objects are absent — the named open legs, not hand-waves.**

## Revelation (collapse — K₀ is the SAME group completion as ℤ, one level up; what's NEW vs integers.md)

**Collapse — ℤ and K₀ are ONE construction: the difference-Lens / group completion, at two carriers.**
`integers.md` showed ℤ = `⟨ directed count-pair (m,n) | L₋ = m−n ⟩`, the group completion of `(ℕ,+)`.
K₀ is the *identical* normal form with the carrier enriched: `⟨ directed object-pair ([A],[B]) over
(iso-classes,⊕) | L₋ = [A]−[B] ⟩`. The forcing sentence is one: **ask the monoid `(iso-classes, ⊕)` to be
closed under the difference-reading, and the group completion is forced** — there is no exterior dialer
adding "virtual objects" `−[A]`; you are reading the *already-present* pair construction through `L₋`, the
same `L₋` that ℤ is. The "virtual bundle" `−[A]` that K-theory is famous for is *not* a new substance — it
is the pair-swap bit of `C` read by `L₋`, exactly `integers.md`'s "negative is not a substance". The
miracle of K₀ (formal differences of objects) is `integers.md`'s miracle (formal differences of counts)
verbatim.

**The NEW datum vs `integers.md` (this is why the note is not a re-skin):** `integers.md` argued the
difference-Lens *for ℕ-counts* and flagged it as the answer to a CLAUDE.md failure-mode. This note's new
content is twofold and both Lean-grounded:
1. **The repo's group-completion theorem is parametrized over an arbitrary `CommCancelSemigroup` `M`** —
   so the lift from ℕ-counts to a monoid of *objects* is not analogy but *the same theorem at a different
   `M`* (`invert_is_the_universal_group_completion`, with `addCCS` the ℕ instance and an object-`⊕` monoid
   the K-theory instance). The universal property — "every additive invariant factors through K₀" — IS
   `lift_unique`, already proved choice-free. *This is the genuinely new structural fact:* the difference-
   Lens is not tied to ℕ; it is a functor of the carrier monoid, and the repo built it that way.
2. **K₀'s two extra ingredients beyond bare ℤ are each an already-decomposed leg:** the rank character is
   `dimension.md`/`prime_factorization`'s `×↦+` arrow (`vp_mul`), and the short-exact relation is
   `homological_algebra.md`'s `q=+1` exact pole (`reduced_betti_d4_contractible`). So K₀ = (difference-Lens
   = `integers.md`) ⊕ (`×↦+` character = `dimension.md`) ⊕ (exact-sequence `q=+1` = `homological_algebra.md`)
   — three already-built legs, no fourth.

This passes the re-skin guard: it does not re-describe K-theory in new words — it **identifies K₀ with a
theorem the repo already proved for ℤ** (the general-`M` group completion), and identifies its two extra
relations with two already-decomposed characters. The deepest line: **the difference-Lens is carrier-
polymorphic** — group completion is the same `lift` whether the operand monoid is `(ℕ,+)` (giving ℤ),
`(ℚ₊,·)` (the repo's `mulCCS`/`ℚ₊` instance), or `(iso-classes,⊕)` (giving K₀); the universal additive
invariant is just `lift` read at the object-carrier, and "K-theory is hard" is the *carrier* being rich
(plus the `q=−1` higher-`K_n` obstruction), not the *construction* being new. **EXTEND; no new axis;
interior model v7.1 holds.** The one genuine absence — the (iso-classes, ⊕) monoid carrier and the named
`K₀`/`K_n` object — is located precisely: the same shape as `homological_algebra.md`'s missing `Ext^n`
object, the abelian-category twin needed to instantiate the (fully built, general-`M`) group-completion
engine.

## Note for the technique

**No new primitive; K₀ consolidates `integers.md` + `dimension.md` + `homological_algebra.md` and supplies
one sharpening of the model: the difference-Lens / group completion is CARRIER-POLYMORPHIC.** `integers.md`
left the difference-Lens looking ℕ-specific (count-pairs). K₀ shows — and the repo's `PairCompletionUniversal`
*already proves* — that the group completion is a construction on *any* commutative cancellative monoid:
ℤ (`+`), ℚ₊ (`·`), K₀ (`⊕`) are three carriers of one `lift`. The lesson for the model: the **reading
slot's "difference-Lens `L₋`" carries a carrier parameter** — the monoid whose elements the pair entries
are — exactly as `padic.md` gave the resolution axis a *base* parameter. The character arrow (rank = `×↦+`)
and the `q=±1` residue (K₀ = q=+1 exact / higher K_n = q=−1 obstruction) absorb the rest. This consolidates
the README's "group-completion = the difference-Lens" line from one instance (ℤ) to a *family over the
carrier monoid*, with the universal property (`lift_unique`, choice-free) as the shared engine.

The one genuine absence is located precisely: every leg K₀ needs *structurally* — the group-completion
universal property (over arbitrary `M`), the difference-Lens, the additive character, the `q=+1` exact
relation, the `q=±1` grading for higher `K_n` — is present and PURE; only the **monoid-of-iso-classes
carrier** (and the named `K₀(C)`/`K_n`/short-exact objects it would feed) is open, the abelian-category
twin of `homological_algebra.md`'s missing `Ext^n`. A buildable witness is named below.

---

## Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity scanned via `tools/scan_axioms.py` from repo root this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **★ K₀ = the group-completion universal property over arbitrary `M` (the difference-Lens one level up)** | `Lens/Number/Nat213/Tower/PairCompletionUniversal.lean:215 invert_is_the_universal_group_completion`, `:83 lift`, `:113 lift_combine`, `:92 lift_respects_pairEquiv`, `:125 lift_eta`, `:169 lift_unique`, `:267 addCCS_completion_is_Int` | ∅-axiom PURE ✓ **scanned 19/0** |
| group completion = "invert is one move" (ℤ at `+`, ℚ₊ at `·`; K₀ the 3rd carrier) | `Lens/Number/Nat213/Tower/PairCompletion.lean:147 invert_is_one_move`, `:81 combine`, `:111 diagonal_is_combine_identity` | ∅-axiom PURE ✓ **scanned 17/0** |
| **★ the difference-Lens `L₋` founding (ℤ = count-Lens on a pair); the "Grothendieck/group law"** | `Lens/Number/DifferenceLensFounding.lean:41 difference_lens_founds_on_count`, `:60 subNatNat_additive` (docstring: "the Grothendieck/group law"), `:74 difference_lens_slash_additive`, `:33 diffView` | ∅-axiom PURE ✓ **scanned 4/0** |
| difference-Lens readout + translation-invariance (the per-reading residue, one level up) | `Lens/Number/Nat213/Tower/NatPairToInt.lean:37 npairToInt`, `:138 npairToInt_translation_invariant`, `:119 npairToInt_diag_shift`; `Meta/Int213/Core.lean:34 neg_subNatNat` (sign = pair-swap) | ∅-axiom PURE ✓ |
| **★ rank/dimension `K₀→ℤ` = the additive character `×↦+` (`⊕↦+`, the `vp_mul` arrow)** | `Lib/Math/NumberTheory/PrimeValuation.lean:96 vp_mul` (`vp(a·b)=vp a+vp b`); `…/Real213/Markov/SternBrocotMarkov.lean:104 det2_mul`; `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77 legendre_mul` | ∅-axiom PURE ✓ (`PrimeValuation` **scanned 7/0**) |
| **★ short-exact `[B]=[A]+[C]` = the `q=+1` exact part (`Ext⁰`, residue empty: `ker=im`)** | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible` | ∅-axiom PURE ✓ **scanned 11/0** |
| **★ K₀ (q=+1 converge) vs higher `K_n` (q=−1 escape obstruction) = the `Ext^{>0}` analogue** | `Lib/Math/Foundations/ResidueTag.lean:228 residue_tag_two_poles`, `:133 escape_residue_outside`, `:160 converge_residue_fixed`, `:86 multiplier_unimodular` | ∅-axiom PURE ✓ **scanned 55/0** |
| split = q=+1 closure (the K₀ exact-relation closure pole) | `Lib/Math/Order/GaloisConnection.lean:126 clo_idempotent` | ∅-axiom PURE ✓ (`galois.md`) |
| cross-frame | `integers.md` (ℤ = difference-Lens on `(ℕ,+)`, the `M=addCCS` case), `dimension.md` (`L↑`/rank = the `×↦+` height-reading), `prime_factorization.md` (`vp_mul` = `×↦·`/`×↦+`), `homological_algebra.md` (`Ext⁰` = q=+1 exact / `Ext^{>0}` = q=−1 obstruction), `groups.md` (Aut-family — the `K_1` automorphism side, conceptual) | prior, ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):**
`E213.Lens.Number.Nat213.Tower.PairCompletionUniversal` **19 pure / 0 dirty**;
`E213.Lens.Number.Nat213.Tower.PairCompletion` **17 pure / 0 dirty**;
`E213.Lens.Number.DifferenceLensFounding` **4 pure / 0 dirty**;
`E213.Lib.Math.NumberTheory.PrimeValuation` **7 pure / 0 dirty**;
`E213.Lib.Math.Cohomology.Examples.BettiKernel` **11 pure / 0 dirty**;
`E213.Lib.Math.Foundations.ResidueTag` **55 pure / 0 dirty**. All PURE.

## Dropped / flagged (honest)

- **`K0` / `GrothendieckGroup` / `KTheory` / `K0Group` OBJECTS — ABSENT, confirmed.** Grep over `lean/E213`
  for `K0`/`GrothendieckGroup`/`KTheory`/`K_theory`/`K0Group` returns **zero declarations** (predicted-not-
  built, confirmed). The named K-theory object does not exist; only the group-completion *engine* it would
  use is built (and that, fully general over `M`).
- **The monoid-of-iso-classes carrier (`isoClass` / `AbelianCategory` / `ShortExact` / `DirectSum` /
  `exact_sequence`) — ABSENT, confirmed.** Grep returns **zero declarations**. There is no `(iso-classes,⊕)`
  monoid to feed `PairCompletionUniversal`'s `M`, no abelian/exact category, no short-exact-sequence type.
  The short-exact relation lives only as the abstract `q=+1` exact condition (`reduced_betti_d4_contractible`),
  not as a relation imposed on a monoid of objects. **This is the precise missing leg** — the abelian-
  category twin of `homological_algebra.md`'s missing `Ext^n`/resolution object.
- **`Grothendieck` hits are docstrings only.** The four `Grothendieck` grep hits (`DifferenceLensFounding.lean:58`,
  `NatPairToInt.lean:115`, `PairCompletionUniversal.lean:23`, `SignedCut/Core/Equivalence.lean:9`) are all
  *narrative comments* naming the construction, not Lean declarations — the field's *name* is in the repo,
  the *object* is not. Cited as such; no theorem claimed from a docstring.
- **`groups.md`'s `Aut`-family as the `K_1` side** — flagged conceptual, not cited as a K-theory anchor.
  `K_1 = GL/E` is the automorphism (Aut-family) side, which `groups.md`'s `PermGroup` decomposes, but no
  `K_1`/`GL`/`elementary-matrix` object exists; left out to avoid overclaiming.

## Named buildable witness (the abelian-category twin of `NonzeroBetti.lean`)

The precise weld is buildable ∅-axiom and small: **instantiate `PairCompletionUniversal`'s `M` with a
concrete commutative monoid of "objects"** — e.g. `(ℕ, +)` *read as `(iso-classes of f.d. vector spaces,
⊕)` via dimension*, or a finite free monoid on a few generators with `⊕ = +` coordinatewise. Then:
- `K₀ = liftZ`-analogue is the rank map, and `invert_is_the_universal_group_completion` *is* "rank is the
  universal additive invariant" — already proved; the witness is just naming the instance `K0_of_vect := …`
  and recording `K0_of_vect ≅ ℤ^rank` as a `decide`/`rfl` corollary.
- A K₀-with-relations witness: take the free monoid on `{[A],[B],[C]}` modulo `[B]=[A]+[C]` (one short-exact
  relation) and show its group completion is `ℤ²` — the `q=+1` exact quotient, the K-theory analogue of
  `NonzeroBetti.lean`'s hollow-triangle `H¹≠0` (here the *exact*/`q=+1` complement: the relation closes,
  residue empty). This welds the (all-built) group-completion engine to a named `K₀` object on a finite
  carrier, exactly the shape `homological_algebra.md` named for `Ext`.
The general (iso-classes, ⊕) carrier over an abelian category remains the open leg (the named-object gap).
