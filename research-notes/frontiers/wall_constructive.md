# Frontier: dissolving the `CompleteMetricModulus.lim` wall (constructive-analysis route)

Status: OPEN idea memo. No Lean edited. Constructive-analysis (Bishop–Bridges)
diagnosis + a concrete ∅-axiom-compatible reform of the Banach engine.

All citations grep/Read-verified against the branch `claude/multi-agent-math-research-3lv3gj`.

---

## (a) Diagnosis — what the wall actually is

`CompleteMetricModulus` bundles two things
(`lean/E213/Lib/Math/Analysis/BanachFixedPoint.lean:183-189`):

```
structure CompleteMetricModulus (X : Type) extends MetricModulus X where
  lim : (Nat → X) → X                                    -- TOTAL, no Cauchy arg
  climconv : ∀ (seq : Nat → X),
    (∀ m, ∃ N, ∀ p q, p ≥ N → q ≥ N → close m (seq p) (seq q)) →   -- bare Cauchy
    ∀ m, ∃ N, ∀ p, p ≥ N → close m (seq p) (lim seq)
```

`lim` takes a **bare** `Nat → X` (no modulus argument) and `climconv` claims it
is correct for *every* sequence that happens to be Cauchy. Note the Cauchy
hypothesis here is the **bare/non-uniform** form `∀m,∃N,...`: the convergence
rate `N(m)` is hidden behind an existential and is *not* an input to `lim`.

The constructive obstruction (the wall): to satisfy `climconv`, a total
choice-free `lim` would have to recover each input sequence's own convergence
rate `N(m)` from the sequence alone. Extracting that rate from the bare
`∀m,∃N` data is exactly an instance of countable choice / an unbounded search
with no decidable stopping rule — not available ∅-axiom. The repo's own
`DyadicCompletion` already documents this: it cannot feed `DyC L` to
`banach_fixed_point` and instead *engineers around* `lim` with the
**stabilizing diagonal** `stab` (`DyadicCompletion.lean:204-257`), a decidable
freeze that is regular-by-construction for *every* `S`. That `stab` machinery
is precisely the cost of forcing a total `lim` onto bare sequences. It works,
but it is a workaround bolted onto a mis-shaped interface, not a clean
instantiation of the generic engine.

Key structural facts confirmed by reading the source:

- `MetricModulus` has exactly **4 fields** `crefl/csymm/cmono/ctri`
  (`UniformLimitContinuous.lean:51-61`); `qtri` is a *derived* theorem
  (`:75-83`), not data. So a metric carries no built-in limit — completeness
  is genuinely the only extra structure at issue.
- `picard_cauchy` (`BanachFixedPoint.lean:154-174`) proves the Picard orbit is
  Cauchy with the **explicit, closed-form modulus `N(m) = m`** (`refine ⟨m, ?_⟩`
  at `:159`). The rate is computed from `m` and the base gap alone — no
  completeness, no `lim`, no search.

So the wall is **not** in `picard_cauchy` and **not** in the contraction; it is
solely in `lim` consuming a bare sequence. The fix is to stop asking `lim` to
guess the modulus and instead **carry the modulus that is already in hand**.

---

## (b) The reform — two layers, cleanest first

### Layer 1 (recommended primary): a modulated engine that needs NO `lim` field at all

The leverage: `picard_cauchy` already hands us the modulus `N(m)=m`. The fixed
point's *content* is "located equality `T x* = x*` to every scale" — and that
content is reached purely by `picard_cauchy` + a `lim` that converges on
**this one orbit** whose modulus we already possess. We do not need a generic
bare-sequence `lim`. Re-signature completeness so `lim` consumes a sequence
**together with its modulus** (a regular/modulated Cauchy sequence), making it
total and choice-free:

```
structure CompleteMetricModulusMod (X : Type) extends MetricModulus X where
  limMod : (seq : Nat → X) → (N : Nat → Nat) →
    (hcau : ∀ m p q, p ≥ N m → q ≥ N m → close m (seq p) (seq q)) → X
  climconvMod : ∀ (seq : Nat → X) (N : Nat → Nat)
    (hcau : ∀ m p q, p ≥ N m → q ≥ N m → close m (seq p) (seq q)),
    ∀ m, ∃ K, ∀ p, p ≥ K → close m (seq p) (limMod seq N hcau)
```

This is the standard Bishop completion shape: `limMod` is total on
*modulated* Cauchy sequences (modulus supplied), so no hidden search. The
generic engine then becomes:

```
theorem banach_fixed_point_modulated
    {X : Type} (C : CompleteMetricModulusMod X) {T : X → X}
    (hT : Contraction C.toMetricModulus T) (x0 : X) (s : Nat)
    (hbase : C.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ m, C.close m
      (C.limMod (picard T x0) (fun m => m) <PicardModProof>)
      (T (C.limMod (picard T x0) (fun m => m) <PicardModProof>))
```

where `<PicardModProof>` is the **uniform** (modulus) repackaging of
`picard_cauchy`. Note `picard_cauchy`'s current conclusion is the bare form
`∀m,∃N,...` (`:156`); the witness it produces is literally `N = m`
(`refine ⟨m,?_⟩`), so a one-line variant `picard_cauchy_mod` of shape

```
theorem picard_cauchy_mod (hT : Contraction M T) (x0 : X) (s : Nat)
    (hbase : M.close (s+1) (picard T x0 0) (picard T x0 1)) :
    ∀ m p q, p ≥ m → q ≥ m → M.close m (picard T x0 p) (picard T x0 q)
```

is obtained by deleting the `∃N` wrapper and inlining `N=m` — the existing
proof body (`close_le_tail` at `:132`, `cmono_le` at `:118`) already proves
exactly this pointwise statement. This `picard_cauchy_mod` is the
`<PicardModProof>` argument (instantiated at `N = fun m => m`).

The proof of `banach_fixed_point_modulated` is the *same* argument as the
current `banach_fixed_point` (`:202-237`): obtain convergence at scales `m+2`
and `m+3` from `climconvMod` instead of `climconv`, drive the contraction, and
chain via `ctri/cmono`. Nothing in that body uses the bare-sequence generality
of `lim`; it only ever applies `climconv` to `picard T x0`. So the rewrite is
mechanical and stays ∅-axiom.

### Layer 2 (alternative): `lim` defined only on the type of regular sequences

A sharper option exploiting that the repo's carrier `DyC L` **is already** the
type of regular Cauchy sequences (`DyadicCompletion.lean:54-58`: `structure DyC`
bundles `seq` with `reg : ∀ m p q, p ≥ m → q ≥ m → closeDy L m (seq p) (seq q)`,
identity modulus). One can give `lim` the type `RegSeq X → X` where `RegSeq`
is "sequence + regular spec at identity modulus". This is Layer 1 specialized
to `N = id`, and matches Bishop's regular-sequence convention exactly. It is
the cleanest *if* one is willing to normalize every Cauchy sequence to identity
modulus first (always possible: subsample `seq ∘ N` is regular). For the
engine we don't even need that normalization because `picard`'s modulus is
already `N(m)=m = id`, i.e. the Picard orbit is *literally a regular sequence
in the Bishop sense*. So for the Banach application, Layer 1 with `N = id`
collapses onto Layer 2 — the orbit is already regular, no subsampling needed.

**Recommendation:** ship `CompleteMetricModulusMod` (Layer 1) as the general
interface and instantiate it at `N = id` for the Picard orbit. It is strictly
more general than Layer 2, costs nothing extra, and the modulus argument is
exactly the data `DyC L.reg` already provides.

---

## (c) Instantiation path for Φ (the convolve-rescale map)

The completion already supplies every piece the modulated engine needs; only
the `limMod`/`climconvMod` fields must be re-pointed at the existing `stab`
machinery (which is *already* modulated-correct):

1. **Carrier + metric**: `metC L : MetricModulus (DyC L)`
   (`DyadicCompletion.lean:90-95`). Reused verbatim.
2. **Contraction**: `Φhat_contraction L : Contraction (metC L) (Φhat L)`
   (`:316-322`). This is the `hT` argument. Already proved, ∅-axiom.
3. **`limMod` field**: `limPoint L S : DyC L` (`:255-257`), built from the
   stabilizing diagonal `stab` (`:222-227`), regular by `stabShift_regular`
   (`:245-250`). Crucially `limPoint` is **total in `S`** and needs no Cauchy
   hypothesis — so it trivially provides `limMod` (ignore, or consume, the
   supplied modulus). The decidable freeze `stab_step` (`:232-239`) keeps it
   constructive.
4. **`climconvMod` field**: the convergence of `stab`/`limPoint` for a genuinely
   Cauchy `S` is the intended content of `climconv` (memo'd at `:24-27`, the
   "3ε / quarter-triangle" argument via `diag_reg` `:116-139` and `metC.qtri`).
   Supplying the modulus as an explicit argument makes that argument *easier*,
   not harder (no `∃N`-extraction needed — the `N` is given).
5. **The orbit + limit**: `orbit_to_center_completion L p`
   (`:354-370`) proves the `Φhat`-orbit from `inj L (p,0)` converges in `closeC`
   to `inj L (0,0)` (the Gaussian center). Combined with
   `banach_fixed_point_modulated`, the center `inj L (0,0)` is exhibited as the
   genuine located fixed point reached as the Picard limit *through the generic
   engine* — closing the gap the file's header (`:7-12`) flags as currently
   unbridgeable.

Net: instantiating `CompleteMetricModulusMod (DyC L)` requires only wrapping the
already-built `limPoint` + its convergence proof as the two fields, then calling
`banach_fixed_point_modulated` with `Φhat_contraction`. No new analysis.

---

## (d) Honest assessment — is it ∅-axiom-achievable?

**Yes, with no residue of choice — and the repo is already 90% there.**

- `banach_fixed_point_modulated` is ∅-axiom: its proof is the current
  `banach_fixed_point` body (`:202-237`), which uses only `ctri/cmono/csymm`,
  `Nat` arithmetic, and `climconv` applied to one explicit sequence. None of
  that touches `Classical`, `propext`, `Quot.sound`, `funext`, or
  `native_decide`. Re-pointing `climconv → climconvMod` changes no proof step.
- `picard_cauchy_mod` is ∅-axiom: it is `picard_cauchy` with the `∃N` wrapper
  deleted and `N=m` inlined; the body already proves the pointwise claim.
- The `limMod` witness is ∅-axiom: `limPoint`/`stab` are built from a
  **decidable** `closeDy` freeze (`instance Decidable (closeDy ...)` at `:218`,
  pure `Nat` `<`) — no choice, no `native_decide`, regular-by-construction.

**Where choice WAS lurking, and why the reform removes it:** the *only* place a
choice principle threatened was the original `lim : (Nat → X) → X` correct on
**bare** Cauchy sequences — recovering the hidden `N(m)` from `∀m,∃N` data is
countable choice. The reform never asks for that: the modulus is an explicit
argument (`limMod ... (N) (hcau)`), and for the Banach application it is the
closed form `N = id` handed over by `picard_cauchy`. **No choice principle
survives; the obstruction is dissolved, not merely relocated.**

**Subtlety to flag (not an obstruction, a design point):** `CompleteMetricModulus`
(bare) and `CompleteMetricModulusMod` are different structures. The honest move
is to *replace* the bare interface with the modulated one (or keep both and mark
the bare `climconv` as the harder-to-inhabit form). The existing `trivComplete`
non-vacuity instance (`:290-293`) re-instantiates trivially under the modulated
interface (everywhere-`True` metric). The `DyC L` instance becomes the first
**non-trivial** inhabitant — which is the actual prize.

**One caveat worth a line in the eventual Lean docstring:** the modulus passed to
`limMod` for the Picard orbit is `N = id`, valid only given the base gap
`hbase : close (s+1) x0 (T x0)`. The engine's signature already carries `hbase`
(`:204`), so this is consistent; the orbit's regularity is conditional on the
base gap exactly as `picard_step_geometric` (`:45`) requires. No hidden
universality is assumed.

---

## Verified citation table

| Claim | Location |
|---|---|
| bare `lim`/`climconv` (the wall) | `BanachFixedPoint.lean:183-189` |
| `MetricModulus` = 4 fields, `qtri` derived | `UniformLimitContinuous.lean:51-61`, `:75-83` |
| `picard_cauchy` witness `N=m` | `BanachFixedPoint.lean:154-174` (`refine ⟨m,?_⟩` `:159`) |
| `close_le_tail`, `cmono_le` (proof body reused) | `BanachFixedPoint.lean:132-142`, `:118-128` |
| current `banach_fixed_point` proof (reused) | `BanachFixedPoint.lean:202-237` |
| `DyC L` = regular Cauchy seq carrier | `DyadicCompletion.lean:54-58` |
| `metC L` completion metric | `DyadicCompletion.lean:90-95` |
| `stab`, `stab_step`, decidable freeze | `DyadicCompletion.lean:218-239` |
| `limPoint` total regular limit | `DyadicCompletion.lean:255-257` |
| `Φhat_contraction` | `DyadicCompletion.lean:316-322` |
| `orbit_to_center_completion` | `DyadicCompletion.lean:354-370` |
| `Φ_contraction`, `orbit_to_center` (Dy level) | `ConvolveRescaleContraction.lean:345`, `:471-473` |
