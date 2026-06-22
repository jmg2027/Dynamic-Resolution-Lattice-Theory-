# Decomposition: the free / growing corner — does the unbounded ascent furnish what the closure monad lacks?

*META-decomposition, per `../README.md` (model v5) and the honest miss of `adjunction.md`: the calculus's
category of readings has so far lived only in the **`q=+1` converging/closure corner** — adjoint
reading-pairs generate the *idempotent* closure monad `clo = G∘F` (`clo_idempotent`, `T²=T`). The
**free/growing corner** (`Lens.bind`/Kleisli/free monad) is un-built. This entry asks the structural
question directly: does the distinguishing's **unbounded ascent** (`MuNuMirror`) furnish the
**non-idempotent, strictly height-raising** endo-reading the closure corner lacks — and is "growing vs
closing" the `q=±1` residue poles again, or a NEW independent axis?*

## The decomposition (C / Reading / Residue) — applied to the calculus's own missing corner

- **Construction `C`** — the bare ascent: the single self-pointing arrow `slash` iterated from the first
  distinguishing. The explicit witness is the primitive tower `rawTower 0 = b`,
  `rawTower (n+1) = slashOrSelf a (rawTower n)` (`PrimitiveTower.rawTower`) — "nothing added at any rung;
  going up a level is the residue pointing at its previous pointing once more."

- **Reading `L↑` (the *endo*-reading, codomain pinned to Raw)** — the same depth/height reading of
  `dimension.md`/`ordinals.md`, but here read as a **self-map** `Raw → Raw`, not a projection to a number.
  The Lean shadow is `foldRaw : Raw → Raw` (`Endomorphic.foldRaw = Raw.fold` at `α := Raw`) — the
  catamorphism whose codomain is the construction type itself. Its primitive successor instance is
  `S r := slashOrSelf Raw.a r` — one more distinguishing laid on top.

- **Residue** — the residue here is the *top* the ascent never reaches: there is no finite Raw of
  unbounded depth (`ascent_unbounded : ∀ N, ∃ r, N < r.depth`), and no νF carrier exists at all (the
  `MuNuMirror` docstring is explicit: "there is **no νF object here**; a native final F-coalgebra is an
  open piece, blocked by Mathlib-free coinduction").

## Re-seeing — the two endo-readings, side by side

```
   CONVERGING corner (built)            GROWING corner (this entry)
   ─────────────────────────            ───────────────────────────
   clo = G∘F  : α → α                   S = (slashOrSelf a ·) : Raw → Raw   (foldRaw-family successor)
   clo_extensive : a ≤ clo a            ascent_adds_unit : depth(S r) = depth r + 1   (strictly raises)
   clo_idempotent : clo(clo a) = clo a  S(S r) ≠ S r        (NEVER idempotent — depth strictly grows)
   T² = T                               Tⁿ strictly increases, never settles (tower_no_cycle, ascent_unbounded)
   residue SETTLES (q=+1)               ascent has NO top (ascent_unbounded); residue REACHED-BY-NONE
```

The closure monad's defining law is `clo(clo a) = clo a` (`clo_idempotent`) — apply twice = apply once,
the reading **settles**. The ascent's defining law is the exact negation: each application strictly
raises depth by the unit (`ascent_adds_unit : (rawTower (n+1)).depth = (rawTower n).depth + 1`), the tower
never returns to an earlier rung (`tower_no_cycle : m ≠ n → rawTower m ≠ rawTower n`), and the depths are
cofinal in ℕ with no finite cap (`ascent_unbounded`). So `S` (and `foldRaw`'s successor instance) is a
genuinely **non-idempotent, strictly height-raising endo-reading** — structurally the mirror image of the
idempotent closure.

## Finding

**1. Does the ascent give the free *corner*? — YES at the level of a non-idempotent height-raising
endo-reading; NO at the level of a *free monad*.** The successor endo-reading `S` is the clean structural
dual of `clo`: `clo_idempotent` (T²=T, settles) versus the strictly-raising, never-cycling, unbounded
ascent (`ascent_adds_unit` + `tower_no_cycle` + `ascent_unbounded`). That is a real, Lean-grounded
*growing* endo-reading `T : Raw → Raw`, and `adjunction.md`'s claim that the calculus has only the
converging corner is, at the **endofunctor/self-map** level, **corrected by this entry**: the growing
self-map exists and is the ascent. But the CT slogan "free *monad*" demands more than a growing
endofunctor — it needs a **multiplication** `μ : T∘T → T` (Kleisli composition / `bind`). The repo has
**no `Lens.bind`, no Kleisli composition, no `μ`** (grep: no `def bind/map/comp/join` in `Lens/LensCore`;
the only `comp` is `DistMorphism.comp`, ordinary morphism composition, not Kleisli). So the ascent
furnishes the **non-idempotent growing endofunctor** the closure corner lacks, but **not** a packaged free
monad. The honest shape: *the free corner's underlying endofunctor is real and is the ascent; the free
corner's monad structure is still un-built.*

**2. Is it the `q=±1` residue poles again, or a NEW axis? — a NEW INDEPENDENT axis.** This is the sharp
finding. The `q=±1` poles are a property of the **residue's self-application** — escape/oscillate
(`q=−1`, `object1_not_surjective`) vs converge-to-fixed-point (`q=+1`, the φ Cassini law). Crucially,
`ordinals.md` already pins `ω` — the residue of *this very ascent* — at **`q=+1`** (the cofinal heights
asymptote *to* ω, an order-type fixed point). So the **converging residue pole and the growing endo-reading
coexist on the same axis-object**: the ascent *grows* (the endo-reading is non-idempotent) while its
*residue converges* (q=+1). Growing-vs-closing therefore **cannot** be the same distinction as `q=±1` —
the ascent is simultaneously "growing" (as an endo-reading) and "q=+1" (as a residue). They are
**orthogonal**:

- **`q=±1`** lives on `Residue(L,C)` — *how the reading's self-application behaves* (escape vs converge).
- **idempotent-vs-growing** lives on the **endo-reading `T : C→C` itself** — *whether iterating the
  reading settles (`T²=T`) or strictly ascends (`depth∘Tⁿ` strictly increasing)*.

So the calculus gains a **second structural axis on the reading slot**: the *iteration character* of an
endo-reading — **idempotent/closing** (`clo`, `T²=T`, `q=+1`-flavored but distinct) vs
**free/growing** (`S`/`foldRaw`-successor, `Tⁿ` strictly raises, never settles). This is the dual of
`homology.md`'s discovery that fold-height is *bidirectional* (∂ runs the height axis down): here the same
height axis, run *up* as a self-map, is the non-idempotent endofunctor — `∂` (down, nilpotent), `clo`
(idempotent), `S` (up, strictly growing) are three iteration-characters of the height reading.

**3. Honest verdict on whether the calculus is only-converging.** It is **not** only-converging at the
endofunctor level — the growing endo-reading is the ascent, and it is fully Lean-grounded. But it **is**
only-converging at the **monad** level: the only *monad* (object with unit + multiplication) the repo
builds is the idempotent closure monad; the free monad's `μ` is genuinely absent, and worse, its natural
home — a completed νF coalgebra — is explicitly flagged as *un-buildable Mathlib-free* (coinduction). So
the limitation `adjunction.md` recorded **shrinks but does not vanish**: the free corner's *functor* is
recovered (the ascent), the free corner's *monad multiplication* remains an honest open target, and the
deepest part (a νF carrier for the completed free object) is not merely un-built but structurally blocked
in the ∅-axiom setting.

## Note for the technique

**Promote a refinement, not a new slogan.** The README's model v5 says "readings form a category … only
its `q=+1` closure corner is built." This entry refines that to: **the reading slot carries an
*iteration-character* axis — idempotent/closing vs free/growing — independent of the residue's `q=±1`
tag.** The closure monad sits at *idempotent*; the ascent (`foldRaw`-successor / `S`) sits at *growing*;
homology's `∂` sits at *nilpotent* — three iteration-characters of the one bidirectional height reading.
The corrected honest edge (replacing `adjunction.md`'s flat "free corner un-built"):

- **Built:** the growing endofunctor `T : Raw → Raw` (the ascent) — non-idempotent, strictly
  height-raising, unbounded, never-cycling. *Grounded.*
- **Open Lean target (small, clean, within reach):** *the successor endo-reading is non-idempotent* —
  the explicit dual of `clo_idempotent`. Concretely:
  `theorem succ_not_idempotent (n) : (slashOrSelf a (slashOrSelf a (rawTower n))) ≠ slashOrSelf a (rawTower n)`
  — provable from `ascent_adds_unit` + `tower_no_cycle` (depth `n+2 ≠ n+1`), no new machinery. This would
  be the q=+1-corner's mirror law stated as a theorem, closing the structural claim of finding 1.
- **Open (genuine, possibly blocked):** the free *monad* `μ : T∘T → T` / Kleisli `bind` — still absent;
  its completed-object home (νF) is flagged un-buildable Mathlib-free. Record as the residual miss.

The deeper payoff: the asymmetry `adjunction.md` named ("a category of residues that converge") was
**conflating two axes**. Separated, the picture is symmetric: the height reading runs *both* directions
(closing/idempotent *and* growing/free), and the residue carries `q=±1` *orthogonally*. The calculus is
**not** stuck in one corner — it has the growing endofunctor; what it lacks is the monad *multiplication*
that would package growth into a free monad, and that lack is the honest, possibly-structural frontier.

---

### Verified Lean anchors (file : theorem) — all grep/Read-confirmed, ∅-axiom-style

The growing endo-reading (the ascent):
- `Theory/Raw/Endomorphic.lean` : `foldRaw` (= `Raw.fold` at `α:=Raw`, the endo-reading `T:Raw→Raw`),
  `foldRaw_slash`, `slashOrSelf` (the total successor combine), `slashOrSelf_self`
  (`slashOrSelf x x = x`), `slashOrSelf_ne_of_ne`, `slashOrSelf_eq_y_iff`
- `Theory/Raw/PrimitiveTower.lean` : `rawTower` (def, `rawTower (n+1) = slashOrSelf a (rawTower n)`),
  `rawTower_depth` (depth tracks level), `depth_and_ne` (`a` never a rung — each slash fires)
- `Theory/Raw/MuNuMirror.lean` : `ascent_adds_unit` (`(rawTower (n+1)).depth = (rawTower n).depth + 1` —
  strictly raises by the unit), `tower_no_cycle` (`m ≠ n → rawTower m ≠ rawTower n` — never settles),
  `ascent_unbounded` (`∀ N, ∃ r, N < r.depth` — no finite cap), `tower_ascent_isPart`,
  `ascent_total_descent_partial`, `descent_wf_ascent_unbounded`; docstring: "there is **no νF object
  here** … blocked by Mathlib-free coinduction"
- `Theory/Raw/Levels.lean` : `Raw.depth_slash` (`(slash x y h).depth = 1 + max x.depth y.depth` — the
  successor `+1` step)

The converging/closure corner (the dual it mirrors):
- `Lib/Math/Order/GaloisConnection.lean` : `clo` (def, `g∘f`), `clo_extensive` (unit), `clo_monotone`,
  `clo_idempotent` (`clo (clo a) = clo a`, `T²=T` — the idempotence the ascent negates)

The `q=±1` residue axis (shown ORTHOGONAL to growing-vs-closing):
- `Lens/Foundations/OneDiagonal.lean` : `no_surjection_of_fixedpointfree` (escape pole, `q=−1`)
- `Lib/Math/Algebra/CassiniUnimodular.lean` : `cassini_law_one_at_two_multipliers` (the `q=±1` two-poles
  law; the ascent's residue `ω` is `q=+1` per `ordinals.md` — converging residue + growing reading coexist)

### Dropped / conceptual-only (honest)

- **`Lens.bind` / Kleisli / free-monad multiplication `μ`** — **DO NOT EXIST.** Grep
  `def bind|map|comp|join` in `Lens/` → only `DistMorphism.comp` (`Lens/Properties/Morphism/Dist.lean`,
  ordinary morphism composition with `comp_assoc`/`id_comp`, **not** Kleisli). The ascent gives the growing
  *endofunctor*, not a free *monad*. Honest open target.
- **νF carrier (a completed free/growing object)** — does not exist and is flagged structurally blocked
  Mathlib-free (`MuNuMirror` docstring). Not merely un-built.
- **`succ_not_idempotent` as a stated theorem** — sketched above as a clean ∅-axiom target
  (`ascent_adds_unit` + `tower_no_cycle`), not yet a named theorem; cited as a target, not as proven.
