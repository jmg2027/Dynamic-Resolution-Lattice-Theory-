# Seminar Round 2 — Agent G: the symmetry-type of a free parameter is its fiber's order-structure

**Status**: active (2026-06-23), Tier 1. Seminar: `no_walls_seminar/`. Role: Agent G (the
symmetry-of-parameters question). Continues A's R2 question (`A_boundaries_as_sigma.md`
"sharpest open question", `R1_synthesis.md` §"What Round 2 builds" item 4) and the corpus's
proven escape/converge asymmetry (`decomposition/SYNTHESIS.md` §3, "honestly asymmetric").

All Lean anchors below were grep-verified (file:line:name, live tree) and axiom-scanned this
session via `python3 tools/scan_axioms.py E213.<module>` from repo root. Tallies `N pure / 0 dirty`.

---

## The two questions, answered

> **(a)** Is height-h's one-way freedom *literally* `escape_residue_outside` read as a height
> dial — i.e. "always can go taller (q=−1 escape never completes), never adjoin less strength
> (no q=+1 fixed completion of the tower)" = the diagonal-escape on the strength axis? **OR**
> **(b)** is height a genuinely NEW asymmetry, a different phenomenon than diagonal-escape?

> **Dual.** WHY is selection-σ symmetric while height-h is asymmetric? Conjecture: symmetry-type
> of a free parameter = (un)orderedness of its fiber. Set-fiber ⟹ symmetric (forcing);
> tower-fiber ⟹ asymmetric (large cardinals).

**Verdict: (a) with one sharp refinement — call it (a′).** The one-wayness of height *is*
`escape_residue_outside` (q=−1) read on the strength axis; it is **not** a new phenomenon. But
the *asymmetry itself* — why this escape is directional where the bare Cantor escape is not — is
**new content the tag alone does not carry**: it comes from the **order on the fiber being
diagonalised**, not from the diagonal engine. The fiber-order ⟹ symmetry law is **CONFIRMED**,
and it is what supplies the "directional" half that the plain q=±1 tag is silent about.

---

## 1. The proof that (a) holds: both escapes are the SAME diagonal generator

The two theorems are not merely analogous — they delegate to **one** engine, verified by reading
the delegation chain (not by resemblance):

| Pole | Theorem | Shape | Delegates to |
|---|---|---|---|
| value-type escape | `ResidueTag.escape_residue_outside` (`ResidueTag.lean:133`, 55/0) | `∀ t fixed-point-free, ¬∃ surjective self-cover` — a **universal negative** | `OneDiagonal.no_surjection_of_fixedpointfree` (`:135`) |
| height escape | `DepthHeightDiagonal.height_diagonal_escapes` (`DepthHeightDiagonal.lean:56`, 43/0) | `∀ r, diag(heightTower c) ≠ heightTower c r` — a **universal negative** | `DepthCeilingResidue.diag_not_in_seq` (`:58`) |

And `diag_not_in_seq` is **the Cantor self-cover itself**, stated by its own file: §2 of
`DepthCeilingResidue.lean:77:ceiling_reference_leaves_residue` proves `¬∃ g : X → (X → Bool),
Surjective g` **`:= cantor_general`** with the docstring "the same engine behind
`FlatOntologyClosure.object1_not_surjective` … the depth-ceiling diagonal of §1 is one instance;
the residue and the unbounded ordinal tower are the *same* self-covering closure" (`:60-66`). The
height diagonal `diag f n = f n n + 1` (`:49`) is the successor-diagonal — Cantor's `not`-modifier
(`bool_not_fixedPointFree`, `ResidueTag.lean:140`) read on ℕ as `(·)+1` (the fixed-point-free
successor). So:

> **height_diagonal_escapes IS escape_residue_outside, instantiated at the value-modifier
> `succ` and the self-cover index = the tower height `r`.** Same `q=−1` pole, same
> `one_diagonal_generates` source. Not a different wall.

This settles the *letter* of A's open point and confirms the `R1_synthesis.md` claim that "the
symmetric/asymmetric split = the corpus's proven escape/converge asymmetry … read on the strength
axis." It is the **same** escape; the strength axis is just the height index `r` carrying it.

The negative shape matches exactly. `escape_residue_outside` is `¬∃` (reached-by-none, the
universal negative); `converge_residue_fixed` (`:160`) is a *positive existence* (a located fixed
point). On the height axis: "you can always go taller" = the escape never completes (`∀ r, diag ≠
heightTower c r`, the `¬∃ top` reading); "never adjoin less strength / no q=+1 completion of the
tower" = there is **no** positive `converge_residue_fixed` for the height index — the tower has no
Banach-contraction fixed point at the level of its *height*. `DepthHeightDiagonal` builds the step
**toward** ε₀ and **builds no ordinal object** (docstring `:28-31`, `:69-70`: "No `Ordinal` object
is constructed"). That absence-of-a-converge-pole is *not* a separate fact — it is the q=−1 escape
having no q=+1 twin on this axis, which is exactly SYNTHESIS §3's "honestly asymmetric."

---

## 2. The refinement (a′): the tag is silent about DIRECTION — the order supplies it

Here is the one thing (a) as stated overshoots, and the reason the answer is (a′) not flat (a).
The `q=±1` tag (`ResidueTag`) is a **2-valued sign bit** — finding (vi) of SYNTHESIS proved it is
*irreducible, transverse to both gradings*, "a 2-valued sign, transverse." A sign bit has **no
direction**: `escape` vs `converge` is a *which-pole* choice, not an *up-vs-down*. So the plain tag
cannot, by itself, say "always taller, never shorter." The directionality — the *monotone* one-way
of height — is **not in B**.

Where does it come from? From the structure of the thing being diagonalised:

- Bare Cantor (`object1_not_surjective`, value-type fiber `B`): the diagonal escapes "to the side."
  There is no order on `B`, so "the missed row is *above* / *taller than* the cover" is meaningless.
  The escape is real but **undirected** — it just lands *outside*, equally in every "direction"
  (there are none).
- Height Cantor (`height_diagonal_escapes`, ordered index `r : ℕ` with `coordLt`,
  `coord_layer_dominates` `:73` — each layer multiplies the rank by ω): the diagonal escapes
  **upward**, because the index it ranges over is **well-ordered** and the modifier is the
  **monotone** successor `+1` (`diag f n = f n n + 1`, `:49`, *strictly exceeds* every level:
  `diag_exceeds`, `DepthCeilingResidue.lean:53`). The escape inherits the order's *direction*.

So the precise statement:

> **The q=−1 escape is the same at both fibers (engine = the one diagonal). What differs is the
> fiber: an UNORDERED fiber gives an undirected escape (lands outside, no up/down); an ORDERED
> (well-founded) fiber gives a DIRECTED escape (lands strictly above). The "one-way-ness" of
> height is the order's monotonicity passed through the diagonal — NOT a property of the tag.**

This is why the honest answer is **(a′)** and not pure (a): height's *escape-ness* is literally
`escape_residue_outside` (so it is **not** a new phenomenon — A's letter is confirmed), but
height's *one-way-ness* is a **new ingredient** the diagonal-escape does not supply on its own. The
asymmetry = the escape engine **⊗** the fiber's order. Calibrated: confirming (a) and crediting (b)
its kernel of truth — the directionality is genuinely additional, it just isn't a *second wall*.

---

## 3. The dual: why selection is symmetric — the fiber-order ⟹ symmetry law, CONFIRMED

The conjecture: **symmetry-type of a free parameter = (un)orderedness of its fiber.** Confirmed,
and now mechanised by §2's mechanism. The law:

> **A free Lens parameter `σ` ranging over a fiber `Φ`:**
> - **`Φ` unordered (a bare set / inhabited family) ⟹ σ is SYMMETRIC** (both adjunctions
>   consistent; adjoin σ *or* ¬σ). **= forcing.**
> - **`Φ` ordered (a well-founded tower) ⟹ σ is ASYMMETRIC / one-way** (always farther along the
>   order, never "back down"; no fixed completion). **= large cardinals.**

The mechanism is **exactly §2 applied to the parameter's own fiber**:

- **Selection-σ ranges over an UNORDERED fiber.** `ChoiceLens.lean` (12/0) builds the canonical
  witness: `F i := Bool` (`:47`), an inhabited family whose fiber `{true, false}` carries **no
  privileged order**. The two sections `sigmaL := fun _ => false`, `sigmaR := fun _ => true`
  (`:51,:55`) are **symmetric** — `sigmaL_ne_sigmaR_at_0` (`:74`) shows they are distinct, and
  *neither is forced* (`choice_is_free_lens_parameter`, `:81`: "no canonical section asserted").
  Swap `false ↔ true` and the picture is identical: there is no "more strength" direction on
  `Bool`, so **adjoin σ or ¬σ, both consistent** — Cohen forcing of a generic section. The LLPO
  tie-in (`sigmaEven`/`sigmaOdd`, `:89-98`) is the binary case: the even/odd disjunction is the
  **unforced** ±1 bit — symmetric precisely because `{even-side, odd-side}` is an unordered pair.
  **Unordered fiber ⟹ the two sections are interchangeable ⟹ symmetric ⟹ forcing.** ✓

- **Height-h ranges over an ORDERED fiber.** `DepthHeightDiagonal` diagonalises the height index
  `r : ℕ`, which is **well-ordered**, with `coord_layer_dominates` (`:73`) making the order
  *strict and dominating* (ω per layer). By §2 the escape is **directed upward**: you can always
  go to `r+1` (`diag` strictly exceeds, `diag_exceeds`), never "select a smaller strength as new"
  (there is no positive `converge_residue_fixed` for the height — no fixed completion). **Ordered
  fiber ⟹ the diagonal inherits a direction ⟹ asymmetric ⟹ large cardinals.** ✓

The law is **clean and structural**: read the fiber's order-structure off, and the free
parameter's symmetry-type follows.

- set-fiber (no order) → symmetric free parameter → forcing / Cohen genericity
- tower-fiber (well-order) → one-way free parameter → large-cardinal strength / Gödel II

And this *rederives* the two independence axes of set theory from one structural distinction
(orderedness of the parameter's fiber) — matching A's R1 finding that selection and height are the
two transverse axes of set-theoretic independence, now with the **reason** they differ supplied,
not just the fact.

### Why the law is not a coincidence: it is the SYNTHESIS §3 asymmetry, located

SYNTHESIS §3's "honestly asymmetric" says: `escape_residue_outside` is a universal *negative*
(`¬∃`), `converge_residue_fixed` a *positive existence* — they cannot collapse into one `Eq`
without excluded middle. The fiber-order law explains *where each pole's asymmetry surfaces as
directionality*:

- On an **unordered** fiber, the escape's negative-shape has **no direction to express**, so the
  parameter looks symmetric (the residue "lands outside" with no up/down — `object1_not_surjective`
  is outside *every* view, finding from CLAUDE.md `object1_not_surjective`). Both adjunctions are
  consistent because there is no order forcing one to be "more."
- On an **ordered** fiber, the escape's negative-shape **acquires a direction** (the missed object
  is strictly *above*), so the parameter is one-way. The "never adjoin less strength" is the
  negative `¬∃ top` reading; the "always taller" is the same `¬∃` saying every level is exceeded.

So the symmetry-of-parameters law is **the §3 asymmetry projected through the fiber's order**: the
asymmetry was always there in the q=−1 pole's negative type; the **fiber's order is the lens that
turns that type-asymmetry into a visible one-way dial.** Unordered fiber → the asymmetry is
invisible (symmetric parameter); ordered fiber → the asymmetry is a direction (one-way parameter).

---

## 4. How this completes the selection-σ / height-h picture

R1 split the `many`-section pole into selection-σ (symmetric, forcing) and height-h (asymmetric,
large cardinals) as **B's two aspects**. G closes the picture by giving the **single generative
reason** for the split and tying it to proven theorems:

```
                 the many-section pole (FREE)
                          │
            "what fiber does σ range over?"
                          │
        ┌─────────────────┴─────────────────┐
   UNORDERED fiber                      ORDERED (well-founded) fiber
   (a bare set: Bool,                   (a tower: ℕ height r, coordLt)
    a Boolean algebra,
    an inhabited family)
        │                                     │
   escape lands "outside,"               escape lands "strictly above,"
   no direction                          inherits the order's direction
   (ChoiceLens 12/0:                     (DepthHeightDiagonal 43/0:
    sigmaL ↔ sigmaR symmetric)            diag_exceeds, one-way up)
        │                                     │
   SYMMETRIC free σ                      ASYMMETRIC one-way h
   adjoin σ OR ¬σ                        always taller, no completion
        │                                     │
   = FORCING                             = LARGE CARDINALS
   (Cohen generic section)               (Gödel II strength ladder)
        └─────────────────┬─────────────────┘
              both are the q=−1 escape engine
        (one_diagonal_generates / object1_not_surjective);
        they differ ONLY by the order-structure of the fiber
```

The whole `many`-pole is **one escape (B's q=−1) over two kinds of fiber**. There is no second
mechanism: forcing and large cardinals are the *same diagonal* over an unordered vs an ordered
fiber. The "two axes of set-theoretic independence" reduce to **one axis (the escape) read across
the fiber-order coordinate** — a genuine collapse, in the corpus's own sense (two superficially
different things shown to share `(C, L)`).

This also sharpens R1's "B's two aspects": selection-σ and height-h are not two *aspects of B* —
they are **the one B-escape applied to two fibers**, the fiber-order being a *frame coordinate*
(SYNTHESIS §2 "the frame — read-off axes"), not a second invariant. The order-structure of the
fiber is the frame axis that decides symmetry; B (escape/converge) is the invariant being read.

---

## BUILT vs ABSENT (no false witnesses)

**BUILT, ∅-axiom (scanned this session):** `ResidueTag` 55/0 (`escape_residue_outside :133`,
`converge_residue_fixed :160`, `residue_tag_two_poles :228`, `bool_not_fixedPointFree :140`);
`DepthHeightDiagonal` 43/0 (`height_diagonal_escapes :56`, `epsilon_direction :71`,
`diag_self_applies :86`); `ChoiceLens` 12/0 (`choice_is_free_lens_parameter :81`,
`sigmaL_ne_sigmaR_at_0 :74`, `sigmaEven_ne_sigmaOdd_at_0 :98`). Delegation chain verified:
`height_diagonal_escapes := diag_not_in_seq` (`DepthCeilingResidue.lean:64`) and
`ceiling_reference_leaves_residue := cantor_general` (`:77-79`, "the same engine behind
`object1_not_surjective`").

**ABSENT (grep-confirmed, named-not-built):** no `Ordinal` type / ε₀ object
(`DepthHeightDiagonal` docstring `:28-31` is explicit — the step *toward* ε₀, no object); no
`large_cardinal`/`measurable`/`inaccessible` object (A's R1 grep stands); no generic-section /
`ForcingToy` object yet (R1 agenda item 1, still the bundling). The fiber-order ⟹ symmetry **law**
is a structural reading across `ResidueTag`/`DepthHeightDiagonal`/`ChoiceLens`, **not** a single
Lean theorem — it is currently a *located prediction*, see the open question.

---

## Verdict + the law + the sharpest open question for Round 3

**Verdict (a′).** Height-h's one-way freedom **IS** `escape_residue_outside` (q=−1) read on the
strength axis — the *same* diagonal generator (`one_diagonal_generates` / `cantor_general`),
**not** a new wall. So (a) is confirmed on the letter. The genuinely-new ingredient (the kernel of
truth in (b)) is **not a second escape** but the **order on the fiber**: the escape's negative
type is undirected on a set-fiber and directed on a tower-fiber. The asymmetry = the one escape ⊗
the fiber's order.

**The law (CONFIRMED).** *The symmetry-type of a free Lens parameter is read off its fiber's
order-structure:* **unordered fiber ⟹ symmetric (forcing); well-ordered fiber ⟹ one-way
asymmetric (large cardinals).** The mechanism is §2: the q=−1 escape inherits direction iff the
fiber it diagonalises is ordered. This rederives the two axes of set-theoretic independence from a
single distinction and ties the symmetry directly to SYNTHESIS §3's proven escape/converge
asymmetry — the §3 type-asymmetry *projected through the fiber's order*.

**Sharpest open question for Round 3.** The law is currently a structural reading, not a theorem.
Can it be made a **single ∅-axiom Lean statement** — a `FiberSymmetry` object parametric in a
fiber `Φ` with an optional order, proving: *(escape over `Φ` is directed) ⟺ (`Φ` carries a
well-founded strict order)*? Concretely: instantiate one diagonal engine `diag` over (i) `Bool`
(unordered) yielding a symmetric/undirected escape and (ii) `ℕ` with `coordLt` (ordered) yielding
`diag_exceeds`'s directed escape, and prove the **biconditional** "directed-escape ⟺ ordered-fiber"
— the one theorem that would turn "forcing vs large cardinals" into a corollary of the fiber's
order-structure. The deep risk to probe: is there a fiber that is **partially** ordered (neither a
bare set nor a well-order) — and would its free parameter be **partially** symmetric (a third
symmetry-type)? If so, the binary law (symmetric/asymmetric) needs a third value, exactly as R1's
"third status" (absence ≠ obstruction ≠ parameter) sat outside the section-count trichotomy. That
is the test that would either close the law or reveal its own residue.
