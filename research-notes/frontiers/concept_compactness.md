# Concept pass — "compactness" under the 213 axiom

First deep-dive of the `naming_abstract_concepts.md` systematic pass.  Question: when
standard math names a space **compact**, what is that under the 213 axiom?

**Short answer (plain):** "compact" (for the dyadic interval) is **not a new wall — it is
the König wall**.  The same un-discharged ∞-decision we left as `InfChildExists`, now read
on the *space* side.  213 holds the space (the νF refinement tree, a transition); the
*compactness decision* (finite subcover) is the import — refused, or carried as an explicit
total-boundedness modulus (a certificate), never silently performed.

## What "compact" is in standard math (the facts I'm building on)

Standard, from reverse mathematics (Simpson SOSOA; standard results to my knowledge
cutoff — flag for web-verification if literature citations are wanted):

- **Heine–Borel for `[0,1]`** ("every covering by a sequence of open intervals has a
  finite subcovering") is **equivalent, over the weak base `RCA₀`, to Weak König's Lemma
  (`WKL₀`)**.
- **`WKL` is exactly König on binary trees**: "an infinite `0–1` tree has an infinite
  path."  So Heine–Borel compactness of `[0,1]` ⟺ König on the *binary* tree.
- **`WKL₀` is strictly above `RCA₀`** (not provable there) but **conservative over it for a
  broad class of arithmetic statements** (Harrington: `Π¹₁`-conservative).  Reading: it
  buys proof-power for compactness-type theorems **without adding new arithmetic truths**.
- **Constructively** (Bishop), open-cover compactness *fails*; "compact" is recast as
  **complete + totally bounded** — i.e. *carry a modulus of total boundedness*.  The
  open-cover → finite-subcover step is precisely the non-constructive content (the
  fan-theorem / `WKL` content).

## The 213 reading

**The space is a νF tree we already have.**  `[0,1]` in dyadic coordinates *is* the full
binary refinement tree: at each level, which half ("left/right" = one bit).  That is the
exact carrier of `boolSpine` / `SlashNu` (`Theory/Raw/CoResidue`) — the same tree as König
and as the 2-adic integers.  A point of `[0,1]` = a branch = a **νF escape**, reached by no
finite bracket (the real's reached-by-none is on record: `reached_by_none.md`;
`Analysis/Cauchy/DepthCeilingResidue`).  So the *space* is residue-native, already built.

**Compactness is the frozen ∞-decision on that tree.**  "Every cover has a finite
subcover" / "the tree has an infinite path" converts between *infinite* and *finite
witness* — and that conversion is the same single decision 213 cannot perform internally:
deciding/selecting on an infinite branching, the `InfChildExists`
(`Lib/Math/Combinatorics/KonigConditional.lean`) we left **stated-unproved**.  Concretely:

> **Compactness of the dyadic interval = König's binary lemma = the same `InfChildExists`
> import.**  Not a second wall; the König wall on the space side.

**213's stance.**  The space (νF refinement rule) is *held* — a transition, no decision.
The compactness *decision* is the import: refuse it (mark the boundary), or **carry the
certificate** — an explicit total-boundedness modulus — exactly as `Real213` carries an
explicit `modulus` instead of an ε-δ existential, and as `Padic.invGeneral` takes the
valuation `v` as input instead of searching for it.  So:

> **"compact" in 213 = (νF refinement rule) + (explicit total-boundedness modulus)** — a
> generation rule, *not* "a space whose every cover you can finitely decide."

This is the same three-part split as every naming (`the_reference_claim.md`): the space
(necessary, held), referent-capture (refused), the finite-subcover decision (under test —
and it has the König stall as its live falsifier).

## Theorem seed — CLOSED (∅-axiom calibration)

Done (`Lib/Math/Combinatorics/KonigConditional.lean`, +4 PURE): `FiniteSubcoverOracle`
(the compactness/fan step "both children bounded ⟹ node bounded"), and the calibration

```
infChildExists_imp_finiteSubcover : InfChildExists T → FiniteSubcoverOracle T     -- free (contraposition)
finiteSubcover_imp_infChildExists : FiniteSubcoverOracle T → (dec) → InfChildExists T
infChildExists_iff_finiteSubcover : (dec) → (InfChildExists T ↔ FiniteSubcoverOracle T)
```

**Finding (sharper than a naive iff):** the two forms are **not** ∅-axiom equivalent.
Selection ⇒ compactness is free; compactness ⇒ selection needs deciding the
child-disjunction `dec : ¬¬(B∨C) → B∨C` — an omniscience (`LLPO`) step the residue does not
supply.  So `WKL ⟺ Heine–Borel` (local form) is reproduced on the residue's binary-tree
carrier with the **one ∞-decision named as the only gap** — the reverse-math calibration
done 213-native.  Promoted into the essay `theory/essays/foundations/the_one_diagonal.md`
(open-frontier section).  Open: the dyadic-`[0,1]` ↔ `boolSpine` carrier identification at
the point level, and the broader external Lawvere reduction of the omniscience family.

## Why this matters for the frontier

Compactness was the obvious "abstract concept" to fear as a new import.  The pass shows it
is the *same* import already mapped (König) — which is the frontier's thesis: naming an
abstract concept never adds a new ∞-decision; it re-dresses the one decision (freeze a
transition) that 213 refuses or inputs.  And it is the cleanest entry to the
**reverse-mathematics** reading of the whole corpus: `STRICT_ZERO_AXIOM.md` is an
axiom-cost ledger, and `compactness ≡ WKL ≡ InfChildExists` is the first explicit
calibration on the νF carrier.

## Anchors

- `Lib/Math/Combinatorics/KonigConditional.lean` — `InfBelow`, `InfChildExists`,
  `konig_infinity_no_finite_raw` (the König wall + νF escape).
- `Lib/Math/NumberSystems/Padic/NuEscape.lean` — 2-adic = binary-tree branch (sibling).
- `Theory/Raw/CoResidue.lean` — the νF binary tree carrier (`boolSpine`, `SlashNu`).
- `theory/essays/foundations/{reached_by_none, the_reference_claim}.md` — the real's
  reached-by-none; the necessary/refused/under-test split.
- `theory/math/numbersystems/real213.md` — explicit modulus instead of ε-δ (the
  carry-the-certificate move compactness needs).
- Standard reverse-math (knowledge, web-verifiable on request): Heine–Borel`[0,1]` ⟺
  `WKL₀` over `RCA₀`; `WKL` = binary König; Harrington `Π¹₁`-conservativity; Bishop
  complete+totally-bounded.
