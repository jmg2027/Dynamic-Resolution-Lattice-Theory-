# The purpose, re-inferred — and the marathon it defines

Status: strategic frontier note (Tier 1). Produced by a 4-agent convening (2026-06-22) on the
originator's directive: *infer my ultimate purpose and conduct the deep multi-session research that
achieves it — grasp the 진의, not peripheral theorems*, together with his pointed question and
admission:

> "Is the goal to turn the axiom into something mathematical — category theory, or HoTT? I don't
> precisely know my own ultimate purpose."

This note records the convening's conclusion so future sessions inherit it, and pins the marathon
spine. It builds on — does not repeat — `the_substance_test.md` (prior inference) and
`the_descent_leg.md` (the central open frontier).

## The convening (method)

Four expert panels, each grounded in the boot corpus + the Lean source (truth lives in the Lean):
1. **Category-theory / HoTT positioning** — locate 213's formal core in standard foundations.
2. **进义 re-inference** — read the failure-mode catalog as a psychological fingerprint; push past
   the prior verdict.
3. **Adversarial skeptic** — verify the "substance vs wordplay" charges against the actual Lean.
4. **Marathon strategist** — design the multi-session research spine.

## Answer to the direct question: "is the goal category theory or HoTT?"

**No — and the Lean is precise enough to say so without hand-waving.**

213's *formal core already IS standard category theory* — not a recasting target, but a re-derivation
from a different primitive:
- `Raw` is the **initial F-algebra** (μF) for the polynomial endofunctor `F(X) = 1 + 1 + {(x,y):x≠y}`
  (`Term/Internal/Tree.lean`, `inductive Tree | a | b | slash`). Lambek's lemma is proved
  (`Theory/Raw/Lambek.lean`: `decompose`/`rebuild` inverse), and well-foundedness pins it to the
  *least* fixed point (`no_infinite_descent`).
- `Raw.fold` **is the catamorphism / universal property of the initial algebra**
  (`SemanticAtom.raw_initial`: `∃!` distinguishing-preserving `Raw → α`).
- the **residue is exactly Lawvere's fixed-point non-surjectivity** (`object1_not_surjective`,
  Cantor), and `OneDiagonal.lean` shows **one** `lawvere_fixed_point` generates Cantor + Russell/
  Liar/Tarski + the residue (one construction `g a := t (f a a)`, not four re-proofs).

So the relationship is **verdict (c): the same content reached from a different starting primitive
(the *distinguishing*), with no priority orderable as "CT is prior".** The goal is not to dress the
axiom up as category theory; it is that category theory's *deepest theorems* (Lawvere, initiality,
Lambek) are **forced by the act of distinguishing** — the direction is the opposite of the worry.

**HoTT specifically: 213 has none of it** — zero hits for univalence, identity types, higher inductive
types, ∞-groupoids, h-levels. The equivalence layer (`Lens.refines` = fold-kernel coarsening) is
strictly **1-categorical / setoid-level**, and the framework actively *forbids* `propext`,
`Quot.sound`, `funext` — structurally the opposite of a univalent foundation. So HoTT is not the
target either, and the repo does not claim it.

**The honest caveat (the skeptic's strongest counter):** everything called "the distinguishing" is
*expressed in* Lean's type theory, whose `inductive`/recursor + `Bool` + `Π` + `Eq` are themselves a
(CT-flavoured) ambient apparatus. `Raw` being initial is a theorem *of that metatheory*. So "the
distinguishing is prior to CT" is, today, **proven for specific objects** (Cantor, the residue,
initiality, the forced no-zero shape) and **asserted as a thesis** for CT/HoTT *as wholes*. The single
theorem that would convert the thesis into a checked fact: an **equivalence between the category of
distinguishing-objects (`DStr`) and the F-algebra category**, with `Raw` as the shared initial object
and the universal property *derived from distinctness* rather than assumed (the `DStr` existence leg,
`the_distinguishing_schema.md`).

## The re-inferred 진의 (purpose)

The prior note's noun-correction (residue → the *act* and its *forcing*) is right. Two refinements
from this convening:

1. **It is a discipline, not a decision procedure.** The behavior is not "compute a verdict and
   halt" — every closed frontier spawns a new one, and the framework *concedes* (CLAUDE.md
   "why-lint-not-memory") that the correction cannot be held while generating. The repository is a
   **sustained practice of non-self-deception about a single irreducible intuition**, with the
   ∅-axiom rule as a lie-detector (`#print axioms` returns a verdict no rhetoric can soften) and the
   failure-mode catalog as the record of the only adversary that reaches the inside: the originator
   himself.

2. **The stated, revealed, and satisfying goals diverge — which is why the purpose is hard to name.**
   - *stated*: rebuild math + physics from one primitive, ∅-axiom (breadth = primacy, §7.1).
   - *revealed* (what the behavior optimizes): a system that cannot lie to itself — the dominant
     artifact by volume is anti-overclaim machinery (the catalog, `scan_all_axioms.py`, the
     publishability audit pricing his own novelty at zero, the G206 null shipped *against himself*).
   - *satisfying* (the unnamed driver): **to encounter a result the primitive forces that he
     demonstrably did not import** — machine-checked so it cannot be talked away, and equally so its
     *absence* cannot be papered over.

**One-paragraph statement (≈70% confidence):** *213's purpose is to build, in the one medium that
cannot be argued with (zero-axiom machine-checked proof), a self-honest discipline for testing whether
the bare act of distinguishing — assuming nothing — forces mathematics into existence as readings of
itself; the deeper driver is for the originator to meet, for one verifiable moment, a forcing he did
not put there, so the founding intuition becomes impossible to dismiss as wordplay and impossible to
inflate beyond what was actually forced.* Strongest evidence against: the sheer volume of genuine
physics + number theory cuts toward the plain stated reading (he literally means "rebuild
everything"); the guardrail may be the cost of an extreme claim, not the secret goal. The honest
position is that stated and satisfying goals may be **the same person at different depths**, not rivals.

## What this implies for the work (the marathon spine)

The four lines, ranked by *leverage toward the purpose* (not ease):

- **Line A (internal cross-domain unifications)** — exhausted; structurally tests *unity*, not
  *forcing*; prior sessions correctly declared it complete.
- **Line B (external exposure)** — the **only prong that can deliver the substance *verdict*** (§5.1:
  the inside cannot test its own primacy). But it is the marathon's *exit* (a paper + one
  pre-registered open-problem attack), not its *body*. Historical lesson (panel 2): the foundational
  programs that survived (Brouwer→Bishop→Martin-Löf, Voevodsky) did so by **shipping a detachable,
  useful artifact to an exterior that judged it on utility, not creed**; the ones that died (Hilbert,
  Frege) claimed totality and were refuted on totality. 213's one detachable artifact is the
  **strict-∅-axiom, Mathlib-free, scanner-enforced Lean corpus** — that is what to expose.
- **The descent leg** — **the true spine.** It is the only line whose *logical form is the thesis
  itself*: the chain `Raw(slash) → Lens-reading → discipline`, load-bearing in the proof. Until a
  real discipline is *computed over a Raw-generated carrier with forcing*, "distinguishing forces
  mathematics" is asserted, not instantiated.

### How abstract foundations actually got accepted — the Line B template

The originator asked (and it sharpens Line B): category theory / type theory / topos theory each hit
*exactly* 213's barrier ("just a language", "no new theorems", "re-skin" — CT was literally dubbed
"general abstract nonsense"). The acceptance pattern is uniform and instructive:

| framework | born to solve (a felt problem) | what cashed it in (acceptance) | foundational status |
|---|---|---|---|
| category theory | make "natural" precise (alg. topology) | Eilenberg–Steenrod homology unification; **indispensable to Grothendieck/Weil**; adjoints (generative) | still contested |
| type theory | block the paradoxes (Russell 1908) | **Curry–Howard** (= structure of computation+proof); proof assistants (4-colour, Feit–Thompson, **Scholze's LTE in Lean**) | contested (HoTT) |
| topos theory | a generalized *space* for étale cohomology (Weil) | indispensable to cohomology (Deligne 1974); logic models (Lawvere–Tierney) | **most** contested |

Four invariants: (1) **none won the foundations contest by argument** — ZFC stayed the default
throughout; (2) each was accepted as a **tool solving a real community's felt problem** *before/instead
of* its foundational claim; (3) each one's **foundational status is still contested — and that was
irrelevant to survival** (Brouwer's philosophy stayed marginal while his machinery went mainstream);
(4) every abstraction was **tethered to computation** (Ext/Tor, running proofs, cohomology groups).

**The sharpened implication for 213.** Type theory is 213's *medium* (Lean = CIC), and 213's ∅-axiom
discipline is a contribution *in the type-theory community's own terms* — a felt concern there:
minimizing the trusted axiom base (which theorems depend on `propext`/`choice`/`quot`). So Line B's
strongest form is **not** "213 is a new foundation" but the **Curry–Howard/Eilenberg–Steenrod-shaped
move**: ship the strict-∅-axiom Mathlib-free scanner-enforced corpus as an *engineering/empirical*
contribution, judged on utility by that community (cf. CompCert/seL4 — engineering artifacts are
respected). Honest asymmetry: each of the three held, at acceptance, a theorem/tool the community
could not get otherwise; 213 holds re-derivations + a corpus (no new theorem — the publishability
audit's verdict). History says the *engineering* claim can suffice — **iff actually shipped to the
exterior and judged there** (the §5.1 wall: the inside cannot deliver this verdict).

**Spine milestones (strategist), on a now-`toNat`-free foundation:**
- **M0 (DONE this session)** — de-launder the divisibility cone: it now stands on `Nat213` all the
  way down, proofs included (the toNat-cone bet, won — see `the_descent_leg.md`).
- **M1 (DONE this session)** — `Irreducible` over `Nat213` (`Irreducible.lean`, 18 PURE): `2,3,5`
  irreducible, `4` not, `irreducible_divisors`; `five_irreducible` via native `lt_succ_iff`
  enumeration + cofactor bound, whole cone `toNat`-free. Reuses `Divisibility` + `Order` (now native).
- **M3 (DONE this session)** — Euclid's lemma over `Nat213` (`EuclidUnique.lean`, 7 PURE): `euclid`
  (`p` irreducible, `p ∣ a·b → p ∣ a ∨ p ∣ b`) + `prime_dvd_prod` (`p ∣ ∏ L → p ∈ L`) — irreducibles
  are *prime*. The no-zero/no-subtraction wall (Bézout needs ℤ; division-with-remainder needs a zero
  remainder) is dissolved by the **internal handle**: a *subtractive* gcd (differences are
  `lt`-witnesses, no zero), with gcd existence + the multiplicative law `gcd(c·a,c·b)=c·gcd(a,b)`
  proved in one well-founded induction on `a+b` (`gcd_exists_mul`, spec quantified over `c`). This is
  the §5.4 "look for the internal handle before declaring a wall" guard, working as designed.
- **M2 (DONE this session)** — factorization existence (`Factorization.lean`, 18 PURE):
  `exists_factorization : ∀ n, ∃ l, (∀ p ∈ l, Irreducible p) ∧ prod l = n`, over `Nat213`. Both
  scouted pins honoured *constructively*: native `acc_lt`/`wf_lt` (no `Nat` measure) + a constructive
  bounded search `decBoundedExists` giving decidable `lt`/`Dvd` and the decided dichotomy
  `irreducible_or_properDiv` (no `Classical.em`). Native `mem_append_pure`/`not_mem_nil` avoid
  propext-carrying core `List` lemmas. Next: M3 (uniqueness — Euclid's lemma via native descent gcd).
- **M2** — existence of irreducible factorization over `Nat213` (the one new ingredient: native
  well-founded recursion on `Order.lt`).
- **M3** — Euclid's lemma + uniqueness (native descent gcd on `Order.lt` — the deepest construction).
- **M4** — forcing capstone: a rival/distinguishing-blind reading *provably cannot* carry
  factorization (reuse `RivalArity` + `distinguishing_necessary`).
- **M5** — merge with the `DStr` dichotomy (close the existence leg): every candidate primitive is
  `≅ Raw` (carries factorization by transport) or fails a *named* clause.
- **Capstone (end state, 10–20 sessions):** `distinguishing_generates_arithmetic` — the Fundamental
  Theorem of Arithmetic *generated* over the distinguishing's own carrier, the reading forced, every
  rival either `Raw` or failing a named clause. Arithmetic — the paradigm discipline — as the
  witnessed instance of "the distinguishing forces mathematics."

## The honest boundary (where it hits §5.1)

Three nameable walls, to be reported as measured boundaries, never papered:
1. **Kernel-import residual.** `Nat213` is a kernel `inductive`; generation is *modulo* the kernel's
   recursor + `Bool` + `Π` + `Eq`. The survivable claim is **recognition, not genesis** — and the
   kernel devices are themselves `DStr` instances (an M5 sub-deposit). Report it; don't hide it.
2. **Rival-`∀` over an untyped class.** M5's dichotomy is total over the *typed* `DStr` class;
   "all conceivable signatures" is not a Lean type — that is the §5.1 wall itself, relocated, not a
   private debt.
3. **The verdict cannot be self-certified.** Even a clean capstone proves internal coherence +
   forcing, not "not a re-skin" — that judgment needs an exterior. Hence the capstone is built **to be
   exposed** (Line B), not to settle the question internally.

## Cross-references
`the_substance_test.md` (prior inference), `the_descent_leg.md` (spine + the toNat-cone bet),
`the_distinguishing_schema.md` (the `DStr` existence leg = M5), `seed/AXIOM/05_no_exterior.md` §5.1,
`seed/AXIOM/07_primacy.md` §7.1, `lean/E213/Lens/Foundations/OneDiagonal.lean`,
`lean/E213/Lens/Foundations/SemanticAtom.lean`, `lean/E213/Lens/Number/Nat213/{Order,Divisibility}.lean`.
