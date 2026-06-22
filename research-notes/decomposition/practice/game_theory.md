# Decomposition: combinatorial game theory (Nim, Sprague–Grundy, nim-value/mex, game-sum = XOR)

*213-decomposition of impartial combinatorial games — a position `g`, its options, the Grundy/nim-value
`G(g) = mex{G(g') : g' an option}`, the Sprague–Grundy theorem ("every impartial game = a Nim-heap of size
`G(g)`"), and game-sum `G(g+h) = G(g) ⊕ G(h)` — per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the
two invariants, the q=±1 spine). The leverage hypothesis: combinatorial game theory is not a new field for
the calculus — it **consolidates three already-decomposed pieces** under the q=±1 tag: surreal.md's `C`
(the directed iterated distinguishing), parity.md's character arrow in its **XOR/𝔽₂ form**, and the
fold-to-normal-form machinery (`Raw.fold`/`raw_initial`). Honest grounding note up front: **no
`Game`/`Nim`/`Grundy` object exists in `lean/E213`** (grep-confirmed below; `mex` *itself* is now built —
`Lib/Math/Combinatorics/Mex.lean`, see anchors — but not yet applied on a `Game` type) — exactly the same
absence surreal.md and knots.md recorded. The Lean-built legs are the directed distinguishing, the XOR
character, the fold-to-normal-form, and the diagonal/least-missing engine; the named game object is the
missing conceptual leg.*

## The decomposition

- **Construction `C`** — **iterated two-sided distinguishing, played out** = surreal.md's `C` *exactly*.
  A game position `g = ⟨ G^L | G^R ⟩` distinguishes its left-options from its right-options; recursing,
  each option is itself an earlier `⟨ · | · ⟩`. This is `Raw`'s slash with the slot ordered (the
  direction bit) and set-valued (options-per-side) — the *identical* carrier surreal.md confirmed
  Conway wrote term-for-term. An **impartial game** is the **symmetric case** `G^L = G^R`: the move-set
  does not depend on whose turn it is, so the L/R direction bit is *trivialized* — `Raw.slash`'s native
  symmetry (`Raw.slash_comm : x/y = y/x`, `Theory/Raw/Slash.lean:40`) re-surfacing. Partizan games keep the direction
  bit live (= surreals); impartial games collapse it (= the symmetric slash), which is *why* impartial
  games carry a single Nat (the nim-value) rather than a signed/ordered surreal value.

- **Reading `L_mex`** — the **Grundy/nim-value reading**: fold a position to a Nat by `G(g) =
  mex{G(g') : g' an option}`, where `mex S` = the **minimal excludant** = the least Nat *not* in `S`.
  This is the count-reading (cardinality.md) re-entering itself with a twist: it reads each position's
  *options' readouts* and returns **the first value the option-set misses**. `mex` is the bounded,
  finite cousin of cardinality.md's diagonal — "the value outside the image" read on a *finite* set, so
  it always lands at a finite Nat (the first gap) rather than escaping to an uncountable residue. The
  reading is a **catamorphism** (`Raw.fold`-style): it is defined by recursion over the build's
  options, exactly the `Lens.view = Raw.fold` shape (`raw_initial`, `SemanticAtom.lean:412`).

- **Residue** — two stratified residues, both q=±1-tagged:
  1. *per-position, the mex gap* — `mex` returns the least Nat **not reachable** in one move. This is the
     q=−1 *escape* residue read at finite resolution: the option-reading forces a value outside its own
     image (the diagonal `no_surjection_of_fixedpointfree`, `OneDiagonal.lean:51`), but on a finite
     option-set the "outside" is a *finite gap*, the first missing Nat. mex = a **bounded diagonal**.
  2. *the win/loss residue* — `G(g) = 0` (a **P-position**, previous/second player wins: no move escapes
     to a `G=0` position, every move *enters* a winning region) is the **q=+1 converging fixed point**;
     `G(g) ≠ 0` (an **N-position**, next/first player wins) is the **q=−1 escape** (a move *exists* to a
     `G=0` position — a winning move out). The whole game-tree flows toward `G=0` sinks the way φ
     asymptotes to its fixed point (`golden_is_converge`, `ResidueTag.lean:180`).

## Re-seeing — `⟨C | L_mex⟩ ⊕ Residue(q=±1)`

```
  impartial game g     =  ⟨ symmetric iterated distinguishing (G^L=G^R) | — ⟩   (surreal.md's C, swap trivial)
  partizan game        =  ⟨ directed (G^L≠G^R) distinguishing | — ⟩            (= surreal.md exactly, swap live)
  nim-value G(g)       =  ⟨ g | L_mex = mex∘(fold over options) ⟩              (Raw.fold catamorphism to a Nat)
  mex{G(g')}           =  the least value NOT in the option-readouts            (bounded diagonal; OneDiagonal at finite res.)
  Sprague–Grundy       =  G is the fold to the canonical Nim-heap *G(g)         (NORMAL FORM: raw_initial / Lens.view=fold)
  game-sum G(g+h)      =  G(g) ⊕ G(h)  (nim-sum = XOR in 𝔽₂^k)                 (parity.md's character, XOR/F2 form)
  P-position G=0       =  the q=+1 converging fixed point (2nd player wins)      (golden_is_converge; ResidueTag)
  N-position G≠0       =  the q=−1 escape: a winning move OUT exists            (no_surjection_of_fixedpointfree)
```

The deepest leg — **game-sum = XOR of nim-values = parity.md's character arrow in its 𝔽₂ form** — is
Lean-grounded, and grounded with a *sharp purity revelation*. The nim-sum on `k`-bit nim-values is
addition in 𝔽₂^k = pointwise `Bool.xor`. The repo has exactly this object, PURE:
`BoolXORFold.psiNatPos` (the XOR-fold over a `Nat → Bool` family) and **`psiNatPos_linear`**
(`BoolXORFold.lean:38`, 6/0 PURE): the fold **distributes over pointwise XOR** —
`Ψ(v ⊕ w) = Ψ(v) ⊕ Ψ(w)` — which is precisely "the nim-value of a sum is the XOR of the nim-values,"
the character homomorphism `(+, game-sum) ↦ (⊕, 𝔽₂)`. The group `(𝔽₂^k, ⊕)` is built PURE as the
pointwise-XOR group `C2_6.mul` (`AutKGroup.lean:82`, `Fin 6 → Bool`, each element self-inverse —
the disjunctive-sum's involution `g + g = 0`).

## Revelation (collapse + forcing + the q=±1 spine, with a purity revelation)

**Combinatorial game theory consolidates surreal + parity + the fold/normal-form machinery under the
q=±1 tag — and the Sprague–Grundy theorem is the XOR-character normal-form theorem with `G=0` = the q=+1
P-position.** Three independent prior decompositions fuse into one with no new primitive:

1. **The game IS surreal.md's `C`.** A game = `⟨position | move-reading⟩` is term-for-term surreal.md's
   directed iterated distinguishing; an impartial game is the **symmetric** special case (`G^L = G^R`),
   which trivializes the direction bit (`Raw.slash_comm`, `Theory/Raw/Slash.lean:40`) — *forcing* the impartial value to
   be a single unsigned Nat (the nim-value) rather than a signed surreal. The L/R asymmetry surreals
   keep is exactly the asymmetry impartial games drop; "partizan vs impartial" is "swap-bit live vs
   swap-bit trivial," one toggle of `C`'s direction sub-structure.

2. **Sprague–Grundy = the fold-to-normal-form theorem.** "Every impartial game equals a Nim-heap of
   size `G(g)`" is the statement that `G` is the **unique catamorphism to the canonical representative**
   — the same `raw_initial`/`Lens.view = Raw.fold` initiality (`SemanticAtom.lean:412`,
   `dhom_unique_pointwise` `UniversalDistinguishing.lean:103`) that makes every build reduce to a normal
   form. The Nim-heap `*n` is the normal form of the game monoid; `G` is the fold; uniqueness (every
   game has exactly one nim-value) is initiality's uniqueness clause. Sprague–Grundy is *not* a new kind
   of theorem — it is the calculus's standard "the read-op is the unique arrow out of `Raw`," instanced
   on the game monoid. (This ties the FreeReduction/colimit normal-form school the SYNTHESIS records:
   `Unified.LensImage`'s `proj_val_eq_iff` is the axiom-free quotient-to-normal-form the game uses, well-
   founded by `no_infinite_descent` — games are finite, so termination is free and a `normalize` exists,
   = the Side-A *confluent + terminating* case of the colimit synthesis.)

3. **Game-sum = the XOR character; P-positions = the q=+1 pole. (The leverage.)** `G(g+h) = G(g) ⊕ G(h)`
   is parity.md's `×↦{±1}` / mod-2 character read on the *disjunctive sum* of games, valued in 𝔽₂^k
   instead of {±1}: it is the **same construction-preserving finite reading** Zolotarev's lemma certifies
   (`psign_mulPerm_hom`, `Zolotarev.lean:133`, the sign is multiplicative), pushed from a single bit to a
   bit-vector. The Sprague–Grundy theory **is the character arrow (XOR-valued) on the game monoid** — the
   seventh+ field through which the calculus's central arrow provably runs. And the win/loss split is the
   q=±1 residue: `G=0` (P-position) = the **converging fixed point** (every move leaves the sink, the
   game flows *toward* `0` — `golden_is_converge`, `ResidueTag.lean:180`); `G≠0` (N-position) = the
   **escape** (a move OUT to `G=0` exists — `no_surjection_of_fixedpointfree`, `OneDiagonal.lean:51`).
   Mex itself is this escape at finite resolution: it returns the *first value the options miss* = a
   bounded diagonal, the finite cousin of cardinality.md's "value outside the image."

**★ The purity revelation (the genuinely new datum this decomposition surfaces).** The nim-sum is PURE
*only in its pointwise/bit-vector form*, not its packed form — and the repo already records exactly this
boundary. `AutKGroup.lean:71-72` states plainly: the packed `Fin 64` nim-sum **via `Nat.xor` brings
`propext`/`Quot.sound`** (DIRTY, through Lean-core `Nat.xor_assoc`), so the corpus uses the **pointwise
`Fin 6 → Bool`** representation to keep the group axioms PURE (`C2_6.mul`, `psiNatPos_linear`). Read
through the calculus this is not an implementation accident: the nim-sum is the character into 𝔽₂^k, and
**a character is PURE exactly when read coordinatewise (per-bit `Bool`/`decide`) and DIRTY when read as
a packed `Nat` value** — the same PURE/DIRTY = Bool/Prop = constructive/classical boundary the
self-description chapter (`topos.md`, SYNTHESIS §6) identifies as 213's internal Heyting/Boolean line.
So combinatorial game theory lands the calculus's central arrow *on the exact corner where its purity
boundary lives*: the nim-value is a 𝔽₂^k character, and it stays in the q=+1 PURE corner only as a
bit-vector. The "XOR is associative, so disjunctive sum is a commutative monoid" fact is the character
homomorphism, and its purity is the calculus's own constructive boundary made concrete.

**Collapse achieved.** Nim, surreals, parity/Zolotarev, and the normal-form/initiality machinery — four
things taught in four courses — are **one `⟨C | L⟩ ⊕ Residue(q=±1)`**: surreal's directed distinguishing
(`C`, swap toggled off for impartial), the mex-fold to the canonical Nim-heap (`L_mex` = the normal-form
catamorphism), the XOR character (`G(g+h)=G(g)⊕G(h)` = parity's arrow in 𝔽₂^k), and the win/loss split
(`G=0`/`G≠0` = the q=+1/q=−1 poles). The calculus did not need a game primitive; it needed the toggle
that turns surreals impartial, plus the character arrow it already owns.

## Note for the technique — does combinatorial game theory VALIDATE the calculus?

**EXTEND by consolidation — a strong leverage entry, no new primitive, with one genuinely new purity
datum.** Reasons it is confirmation, not stress:

1. **No new axis.** Every piece reuses a built one: `C` = surreal.md's directed distinguishing (impartial
   = the symmetric/swap-off case); `L_mex` = the `Raw.fold` catamorphism (`raw_initial`); game-sum = the
   XOR character (`psiNatPos_linear`, `C2_6.mul`); P/N = the q=±1 residue (`golden_is_converge` /
   `no_surjection_of_fixedpointfree`). The model v7.1 carrier covers all of it.
2. **It cashes the surreal–parity bridge.** surreal.md confirmed `C` and named its operations as the open
   ceiling; parity.md owns the character; game theory shows the *impartial* operation (disjunctive sum)
   is exactly parity's character in 𝔽₂^k — so the surreal "arithmetic is unbuilt" ceiling is, *for the
   impartial case*, partially discharged: the sum's character leg is PURE-built (`psiNatPos_linear`),
   even though the recursive game-sum *as an operation on a `Game` type* is not.
3. **It pins the calculus's purity boundary on its central arrow.** The `Nat.xor`-DIRTY /
   `Bool`-pointwise-PURE split (`AutKGroup.lean:71`) is the same constructive boundary as topos.md's
   PURE/DIRTY = Heyting/Boolean line — surfaced here on the nim-sum character itself. That is the
   re-skin-guard-passing revelation: a *new* fact (where the character is PURE) read off the field, not
   a re-description.

**Honest residual / the precise missing leg.** The named **`Game`/`Nim`/`Grundy` object is
ABSENT** from `lean/E213` (grep-confirmed: no `Grundy`, no `\bNim\b`, no `Sprague`; the `mex` *engine* is
now built (`Mex.lean`), but no `Game` type applies it; the
only `game` hits are an unrelated "pattern-catalog game" metaphor in
`Lib/Math/Foundations/PatternCatalog/`). So:
- the **`mex` function** (least Nat not in a finite set) is now **BUILT ∅-axiom**
  (`Lib/Math/Combinatorics/Mex.lean`, 12/0 PURE): `mexFrom`/`mex` (a single linear scan, structural
  recursion on the budget, no `Nat.find`/`omega`/`Classical` — modelled on `BolzanoWeierstrass`'s
  `findFrom`), with `mexFrom_finds` (the scan lands on a non-member = the **bounded diagonal**),
  `mexFrom_lt_mem` (minimality: every smaller value is a member), and
  `mex_eq_zero_iff_zero_excluded` (P-position `G=0` ⟺ `0` is excluded — the q=+1 sink). The mex *engine*
  is now grounded; the missing leg is only its application **on a `Game` type** (below);
- the **recursive `G`-fold on a `Game` type** is not built — its *shape* is `Raw.fold`/`raw_initial`
  (built), but no `Game` inductive carries it;
- the **Sprague–Grundy theorem as a stated `Game ≃ Nim` equivalence** is not built — its *content* is
  the initiality/normal-form theorem (`dhom_unique_pointwise`, built), instanced on a game type that is
  absent;
- the **packed multi-heap nim-sum** is DIRTY (`Nat.xor`); only the **per-bit pointwise** nim-sum is PURE.

This is the identical ceiling surreal.md and knots.md hit — the `C` and the character arrow are confirmed
and PURE-anchored; the **named field object and its arithmetic operation** are the predicted-not-built
target. **Verdict: PREDICTION (leverage) + PARTIAL.** A game = surreal's directed distinguishing
(impartial = swap-trivial); the nim-value = the mex-fold to a canonical Nim-heap (normal form, via
`raw_initial`/`Raw.fold`); game-sum = the XOR/𝔽₂ character arrow (parity, `psiNatPos_linear` PURE);
P-positions `G=0` = the q=+1 fixed point vs N-positions = the q=−1 escape. Combinatorial game theory
**consolidates surreal + parity's character + the normal-form/fold machinery under the q=±1 tag**, with a
new purity-boundary datum on the nim-sum character (and the `mex` engine now BUILT ∅-axiom,
`Mex.lean` 12/0 — the bounded diagonal). 58 decompositions in; EXTEND, no interior break.

---

### Verified Lean anchors (file : line : theorem) — all grep-confirmed; Game/Nim/Grundy ABSENT, mex now BUILT

- **Game/Nim/Grundy ABSENT** (grep over `lean/E213`): `[Gg]rundy` → no files; `\bNim\b|Sprague` → no
  matches; `\b[Gg]ame\b` → only `Lib/Math/Foundations/PatternCatalog/*` ("pattern-catalog game" metaphor,
  unrelated) + `Meta/Tactic/*GuardTest.lean` comments. No `Game`/`Nim` inductive, no `Grundy` function, no
  Sprague–Grundy statement. The named field object is the missing conceptual leg; `mex` itself is now
  built (`Mex.lean`, below) but not yet applied on a `Game` type.

- `Lib/Math/Cohomology/Infrastructure/BoolXORFold.lean:32` : `psiNatPos` (XOR-fold over `Nat → Bool`) and
  **`:38` `psiNatPos_linear`** — `Ψ(v ⊕ w) = Ψ(v) ⊕ Ψ(w)`, the **𝔽₂ character homomorphism = game-sum =
  XOR-of-nim-values**. **PURE** (scanned: 6 pure / 0 dirty); also `xor_pair_swap:25` (XOR AC),
  `psiNatPos_congr_all:52`.
- `Lib/Physics/Symmetry/AutKGroup.lean:82` : `C2_6.mul` (the nim-sum group `(𝔽₂^6, ⊕)` as pointwise
  `Fin 6 → Bool` XOR; `one:79` = `false`, each element self-inverse = the disjunctive-sum involution
  `g+g=0`), PURE. **`:71-72`** : the note that the **packed `Fin 64` nim-sum via `Nat.xor` is DIRTY**
  (`propext`/`Quot.sound` through `Nat.xor_assoc`) — the purity-revelation anchor.
- `Theory/Raw/Slash.lean:40` : `Raw.slash_comm : x/y = y/x` (`Raw.slash` "the distinction", documented at
  `Theory/Raw/API.lean:33-34`) — the bare slash is **symmetric**, so **impartial = the symmetric
  (swap-trivial) case**; partizan keeps the swap live (surreal.md).
- `Lens/Foundations/SemanticAtom.lean:412` : `raw_initial` — `Lens.view = Raw.fold` is the **unique arrow
  out of `Raw`** = the nim-value as the **fold-to-normal-form** (Sprague–Grundy's "= a Nim-heap").
- `Lens/Foundations/UniversalDistinguishing.lean:103` : `dhom_unique_pointwise` — uniqueness of the fold
  = uniqueness of the nim-value (the normal-form clause of Sprague–Grundy).
- `Lens/Foundations/OneDiagonal.lean:44` `lawvere_fixed_point`, **`:51` `no_surjection_of_fixedpointfree`**
  — the diagonal "value outside the image" engine = **mex** at finite resolution (the least-missing Nat)
  and the **N-position q=−1 escape** (a winning move OUT exists). PURE.
- `Lens/Foundations/FlatOntologyClosure.lean:61` : `object1_not_surjective` (the residue = the diagonal at
  `A=Raw`) — the q=−1 escape pole the mex-gap instances at finite resolution.
- `Lib/Math/Foundations/ResidueTag.lean:180` : `golden_is_converge` (q=+1 converging pole = **P-position
  `G=0`**); `:86` `multiplier_unimodular`; `:228` `residue_tag_two_poles` — the formal q=±1 tag the
  P/N split rides.
- `Lib/Math/NumberTheory/ModArith/Zolotarev.lean:133` : `psign_mulPerm_hom` (the sign character is
  multiplicative) — parity.md's character arrow, the {±1}-valued sibling of the 𝔽₂^k nim-sum; `:142`
  `psign_mulPerm_qr`. (Cited PURE across the corpus / `quadratic_reciprocity.md`.)
- `Lib/Math/Combinatorics/Mex.lean` (12/0 PURE) : **`mex` BUILT** — `mexFrom`/`mex` (the least non-member
  within a budget, the **bounded diagonal**), `mexFrom_finds:95`, `mexFrom_lt_mem:72` (minimality),
  `mex_eq_zero_iff_zero_excluded` (P-position `G=0` ⟺ `0` excluded = q=+1 sink). Modelled on
  `BolzanoWeierstrass.lean:26`'s `findFrom` (linear least-witness search, no `Nat.find`).
- `../practice/surreal.md` (the game's `C` = directed iterated distinguishing; impartial = swap-trivial),
  `../practice/parity.md` (the character arrow, here in 𝔽₂^k), `../practice/cardinality.md` (the diagonal
  = mex at finite resolution), `../practice/ordinals.md` (the height ceiling the recursive game-sum hits)
  — the prior decompositions game theory consolidates.

### Dropped / flagged (could not verify or predicted-not-built)

- No Lean `Game`/`Nim`/`Grundy` inductive, no `mex` function, no Sprague–Grundy `Game ≃ Nim` statement,
  no recursive game-sum *operation on a game type* — all flagged predicted-not-built (the honest ceiling,
  identical to surreal.md's transfinite-arithmetic ceiling and knots.md's missing field object). The
  XOR-character leg (`psiNatPos_linear`) and the normal-form leg (`raw_initial`) are PURE-built and
  certify the *structure*; the *named object* is open.
- The **packed** nim-sum (`Nat.xor` over a single Nat) is **DIRTY** (`AutKGroup.lean:71`); only the
  per-bit pointwise `Bool.xor` nim-sum is PURE. Flagged as the purity boundary, not a gap to close.
