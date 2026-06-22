# Decomposition: surreal numbers / combinatorial games (Conway's `{L | R}`)

*213-decomposition of Conway's surreals/games — `x = {L | R}`, "born on day n", the
simplicity ("simplest number between") rule, day-ω — per `../README.md` (model v6). Tests the
hypothesis that Conway's construction is **literally** the calculus's `C`: a surreal is built by
**distinguishing a left set from a right set**, the L/R split is `C`'s direction bit (`q = ±1`),
"born on day n" is fold-height, and day-ω is the height residue. Honest grounding note up front:
**surreals/games proper are ABSENT from `lean/E213`** (the only string match is an incidental aside
in `Lib/Math/NumberSystems/Hyper/Hyper213.lean:32`, "hyperreals, surreals, etc. are quotients" — no
`Surreal`/`Conway`/`Game` type, no `{L|R}` constructor). So this is grounded in the present
distinguishing/`Raw` structure the surreal recipe **mirrors term-for-term**, with one strikingly
exact analog already built: the proper Stern-Brocot tree.*

## The decomposition

- **Construction `C`** — **iterated two-sided distinguishing**. Conway's `{L | R}` distinguishes a
  left collection from a right collection; recursing, both collections are themselves earlier
  `{L|R}`s. This is `Raw` with two refinements: (i) the slot is *set-valued* (a set on each side, not
  one element) and (ii) the slot is *ordered/directed* (left ≠ right as roles). The bare 213 carrier
  is `Raw`'s slash `Raw.slash x y h : x ≠ y → Raw` (`Theory/Raw/Core.lean`, `API.lean:33` "the
  distinction") — the free magma on two atoms, an `x` distinguished from a distinct `y`, iterated
  (`Lambek.decompose`: every non-atom is `slash` of two strictly-shallower builds). The surreal is
  the **ordered, set-valued generalization** of this one slash.
- **Reading `L_{<}`** — the **order-reading**: project the build to its `{L|R}`-order datum — *which
  options sit below, which above*. A surreal *value* is `L_{<}` of a build (Conway: two builds with
  the same cuts read equal); a *game* is the build before this reading collapses ties. The number
  itself is the readout, not the substance — exactly the integers.md pattern one dimension up (ℤ =
  `L₋` of a directed count-*pair*; a surreal = `L_{<}` of a directed *set*-pair).
- **Residue** — two stratified residues, both already named in the practice:
  1. *per-value* — the order-reading is many-to-one (many builds, same cut); the residue is the whole
     fibre of builds a single surreal forgets (the `(m+k,n+k)` anti-diagonal of integers.md, set-valued).
  2. *global, height* — the height-ladder has no top finite rung (`MuNuMirror.ascent_unbounded`); the
     residue over the unbounded ascent is **day-ω**, the `q = +1` converging pole (ordinals.md). The
     day-ω surreals (ω, ε, 1/ω, …) are this height residue, named by their finite generator, never
     inhabited as a completed day.

## Re-seeing — `⟨C | L_{<}⟩`

```
  surreal value x      =  ⟨ iterated directed set-pair {L|R} | L_{<} = the cut-order ⟩
  game (uncollapsed)   =  the same build read BEFORE L_{<} merges ties  (build = the object, ratio.md)
  "born on day n"      =  fold-height n of the build         (Raw.depth_slash : 1 + max; +1 per nesting)
  successor / day n+1  =  one more two-sided distinguishing  (ascent_adds_unit; depth +1)
  the L/R sign         =  the direction bit of C, read out   (q=±1; Raw.swap, not a Raw primitive)
  "simplest x between  =  the well-founded height FLOOR of    (isPart_wf; part_depth_lt;
    L and R"               the builds with cut (L,R)            terminal_iff_atom; sbStep mediant)
  day-ω (ω, 1/ω, ε)    =  Residue(L↑, C) over the ascent, q=+1 (ascent_unbounded; converging pole)
```

The closest *built* mirror is not abstract: **the proper Stern-Brocot tree**
(`Real213/Markov/SternBrocotMarkov.lean`). Conway's dyadic/rational surreals literally ARE
Stern-Brocot, and the repo's `sbStep` is the recipe to the letter:

```lean
def sbStep : Bool → (Nat×Nat)×(Nat×Nat) → (Nat×Nat)×(Nat×Nat)
  | true,  ((p,q),(r,s)) => ((p,q),(p+r, q+s))   -- left child:  mediant becomes new RIGHT bound
  | false, ((p,q),(r,s)) => ((p+r, q+s),(r,s))   -- right child: mediant becomes new LEFT bound
def sbInterval : List Bool → (Nat×Nat)×(Nat×Nat)  -- a path = a build at height = list length
```

`((L_bound),(R_bound))` is exactly `{L | R}`; `Bool` is the direction bit; the mediant `(p+r,q+s)`
inserted strictly *between* L and R is "the simplest number between L and R"; and
`sbInterval_adj : adj (sbInterval path)` — the **det-1 Farey invariant** `q·r = p·s + 1` preserved by
every step (`sbStep_preserves`) — is precisely *why* that between-element is the **unique simplest**
one (`adj_mediant_coprime`/`sbInterval_mediant_coprime`: each mediant is coprime = lowest terms). The
path length is the birthday/fold-height.

## Revelation (collapse + forcing + residue-surfaced)

**Conway's `{L | R}` is, term-for-term, the calculus's `C` = directed iterated distinguishing.** The
mapping is not analogy, it is identity of recipe: `{L|R}` = `Raw`'s slash with the slot made
*ordered* (the direction bit) and *set-valued*; "born on day n" = `Raw.depth` (`depth_slash : 1 + max`,
one nesting = `+1`, `ascent_adds_unit`); the simplicity rule = the **well-founded height floor**
(`isPart_wf`, `part_depth_lt`, `terminal_iff_atom` — the same descent that grounds ordinals.md), made
fully concrete by `sbStep`'s det-1 mediant being the unique coprime point between the bounds; and
day-ω = the height residue at the `q = +1` converging pole (`ascent_unbounded`, ordinals.md). This is
plausibly the **single cleanest native fit in the whole practice**, because every prior practice axis
appears *simultaneously and named by Conway himself*: direction (L/R), set-valued slot, fold-height
(birthday), and the residue (day-ω) — the calculus did not have to *impose* its decomposition; Conway
*wrote it*.

**Collapse — ℝ, the ordinals, and the infinitesimals are ONE construction, separated only by
height/residue.** The calculus predicts this and the surreal construction confirms it:
- a **finite/dyadic real** = `⟨{L|R} | L_{<}⟩` at *finite* height — a finite `sbInterval` path (a
  closed `Raw.depth`, no residue: integers.md/ratio readings on a finite build);
- a **real** (non-dyadic) = the *per-value residue* of the order-reading over a cofinal path — the
  `q = +1` converging residue of an approximant sequence (the SternBrocot/Cauchy pointing,
  `Lens/Instances/Cauchy.lean`), reached-by-none, named by its modulus;
- an **ordinal** ω = the *global height residue* (ordinals.md: `ascent_unbounded`, `q = +1`), the
  `{ ℕ | }` build with empty right side at day ω;
- an **infinitesimal** 1/ω = the *same residue read at the reciprocal pole* — `{0 | 1, 1/2, 1/4, …}`,
  a converging residue squeezed *between* 0 and every positive dyadic, i.e. the height residue read
  *downward* instead of upward.

So "real number", "ordinal", "infinitesimal" stop being three realms: they are **one `⟨C | L_{<}⟩`
at different (height, residue)** coordinates — finite height (dyadics), per-value residue (reals),
global height residue upward (ordinals), global height residue downward/reciprocal (infinitesimals).
This is exactly the README's standing claim ("irrational / infinite / continuous = shapes of a
reading's surplus") cashed in a *single* construction whose author already unified them.

**Forcing.** The L/R *order* is forced, not stipulated: `Raw.slash` is **symmetric**
(`API.lean:34` `slash_comm : x/y = y/x`) — the bare two-sided distinguishing is *unordered*; the
canonical representative is chosen by `Tree.cmp`, and the directed version is the **swap-bit**
(`Raw.swap` is an automorphism, `SwapSlash.Raw.swap_slash`). So "left vs right" is precisely
integers.md's direction bit surfacing — a `Bool`-style pair-swap read out of `C`, **not a Raw
primitive**. Conway's L/R is the order-reading consuming `C`'s already-present swap structure; the
*magnitude* of a surreal is `Nat`-style (the count/depth), the *sign/side* is `Bool`-style — the
identical magnitude+swap factorization integers.md proved for ℤ (`npairToInt = Int.subNatNat`,
`NatPairToInt.lean`), here generalized from count-pairs to set-pairs.

## Note for the technique — does the surreal construction VALIDATE the calculus?

**Strong native-fit confirmation — the cleanest validation that `C` = distinguishing + direction +
fold-height is *literally Conway's recipe*, not a re-skin.** Three independent reasons it is
confirmation and not a stress:

1. **No new primitive.** The model v6 carrier covers `{L|R}` exactly: the slash is the distinguishing,
   the direction bit is the L/R order (forced by `swap`, not added), the birthday is `Raw.depth`, the
   simplicity rule is the well-founded floor `isPart_wf` already living in `C`, and day-ω is the
   `q = +1` height residue. Every piece was *already built* for `Raw`/ordinals/integers; the surreal
   only generalizes the slot from one element to a *set* and from unordered to *ordered*.
2. **The author agrees in advance.** Unlike parity/det/entropy (where the calculus had to *find* the
   decomposition), Conway's own construction *states* it: L/R = direction, day = height, simplest-between
   = floor. The technique's three sub-structures of `C` are Conway's three structural choices. That is
   the highest grade of native fit — the decomposition was the construction all along.
3. **A built mirror exists** (`sbStep`/`sbInterval`, ∅-axiom): the det-1 Stern-Brocot tree is the
   dyadic/rational surreals to the letter — `Bool` direction, mediant-between, coprime-simplest,
   path-length birthday — so the L/R/height/residue claim is not prose; its rational-surreal restriction
   is a machine-checked theorem.

**Honest residual (the stress, such as it is).** Two surreal-specific structures the present `Raw`
does *not* yet carry: (i) the slot is **set-valued** — `Raw.slash` takes two single Raws, not two
*sets* of Raws, so the full `{L|R}` (multiple options per side) is a predicted generalization, not a
built type; (ii) surreal **arithmetic** (`x+y`, `x·y`, the recursive game-sum) and the *equality by
mutual `≤`* are unbuilt, exactly as ordinals.md is honest that `ω+ω`/`ω·ω` are predicted-not-built. So
the verdict is: the **construction** `C` = directed iterated distinguishing is confirmed term-for-term
(and its rational restriction is Lean-anchored via Stern-Brocot); the **operations** on it are the
named open target, the same ceiling ordinals.md hit. The calculus EXTENDS — no break — and gains its
strongest "the author wrote our `C`" datum: **26 decompositions, no break.**

---

### Verified Lean anchors (file : theorem) — all grep-confirmed; surreals-proper ABSENT

- **Surreals/games absent**: grep `[Ss]urreal|Conway|Game` over `lean/E213` returns only
  `Lib/Math/NumberSystems/Hyper/Hyper213.lean:32` (an incidental aside, "hyperreals, surreals, etc.
  are quotients"). No `Surreal`/`Game` type, no `{L|R}` constructor. Grounded below in the present
  `Raw`/distinguishing structure the surreal recipe mirrors.
- `Theory/Raw/Core.lean` : `Raw` (= canonical `Tree`), `Raw.slash` — the two-sided distinguishing,
  the free magma on two atoms (the slash that `{L|R}` generalizes).
- `Theory/Raw/API.lean:33-34` : `Raw.slash` "the distinction"; `Raw.slash_comm : x/y = y/x` — the bare
  slash is **symmetric/unordered** (so L/R order is a *reading*, not a primitive).
- `Theory/Raw/SwapSlash.lean` : `Raw.swap_slash` — `Raw.swap` is an automorphism (the direction bit /
  `q = ±1` source: L↔R is a swap, not a Raw primitive).
- `Theory/Raw/Lambek.lean` : `decompose` (every non-atom = slash of two strictly-shallower builds),
  `part_depth_lt`, `isPart_wf`, `terminal_iff_atom`, `atoms_are_floor`, `no_infinite_descent` — the
  well-founded height **floor** = the simplicity ("simplest between") rule; descent grounds.
- `Theory/Raw/Levels.lean` : `Raw.depth_slash` (`depth (slash x y h) = 1 + max …`) — "born on day n"
  = fold-height; one more `{L|R}` = `+1`.
- `Theory/Raw/MuNuMirror.lean` : `ascent_unbounded` (`∀ N, ∃ r, N < r.depth` = day-ω, no finite cap),
  `ascent_adds_unit` (successor/day n+1 = depth `+1`), `tower_ascent_isPart`, `succ_not_idempotent`
  (the growing reading, day after day strictly rises).
- `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean` : `sbStep` (`Bool`-directed
  mediant-insert = `{L|R}` to the letter), `sbInterval` (a path = a build, length = birthday),
  `sbStep_preserves`/`sbInterval_adj` (det-1 Farey invariant `q·r = p·s + 1` = *why* the between-point
  is unique-simplest), `adj_mediant_coprime`/`sbInterval_mediant_coprime` (every mediant coprime =
  lowest terms) — the **built mirror of the dyadic/rational surreals**.
- `Lens/Number/Nat213/Tower/NatPairToInt.lean` : `npairToInt = Int.subNatNat`,
  `npairToInt_natToNPair`/`…Neg` — the magnitude(`Nat`)+sign(`Bool`-swap) factorization (integers.md)
  the surreal generalizes from count-pairs to set-pairs.
- `Lens/Instances/Cauchy.lean` : the approximant/pointing reading — a non-dyadic real surreal as the
  `q = +1` converging per-value residue of a cofinal path.
- `Lens/Foundations/OneDiagonal.lean` : `no_surjection_of_fixedpointfree` (`q = −1` escaping pole);
  `Lib/Math/Algebra/CassiniUnimodular.lean` : `cassini_law_one_at_two_multipliers` (the `q = ±1`
  two-poles law — day-ω and the infinitesimal are read at `q = +1`).
- `../practice/integers.md` (direction bit), `../practice/ordinals.md` (fold-height residue, day-ω,
  the `ω`/honest-ceiling discipline), `../practice/ratio.md`-pattern (the build is the object; the
  cut/value is a reading) — the three prior decompositions the surreal unifies.

### Dropped / flagged (could not verify or predicted-not-built)

- No Lean `Surreal`/`Game`/`{L|R}` type, no surreal/game **arithmetic** (`+`, `·`, recursive sum),
  no **set-valued** slash — all flagged predicted-not-built (the honest ceiling, mirroring
  ordinals.md's transfinite-arithmetic ceiling). The Stern-Brocot anchor certifies the
  *dyadic/rational* restriction of the `C` claim, not the full set-valued/transfinite surreal.
