# Session Handoff — 2026-07-02

## Branch
`claude/repo-research-context-3utd48` — NOT merged.  6 commits (`31e6aa6..e4c4317`).
New Lean modules build clean; every new declaration **PURE** (`scan_axioms.py`: 15/0 in
`ExteriorAsExtension`, 6/0 in `AperyCollapsing`).

## Headline — the exterior-as-extension arc (originator's conjecture, examined → theorems → live method)

The originator's conjecture — *the "exterior" of no-exterior IS residue-driven system
extension* — was examined against the corpus, **amended, formalized, and converted into a
working attack method** that immediately paid off on the ζ(3) numerator wall.

1. **The amendment (the theory's honest form):** apparent exterior =
   **(extension-capturable component) ⊕ (invariant core — the one wall)**.  Two tower
   shapes proven distinct: progressing (diag towers — yesterday's exterior is today's
   interior) vs fixed-core (`fun _ => true` uncaptured at every re-entry depth).  The
   dynamic face of the no-walls tetrachotomy; §5.7 frozen/dynamic co-present.
2. **Lean (`Lib/Math/Foundations/ExteriorAsExtension.lean`, 15 PURE):** E2 capture
   theorem (`extend`/`tower`, `yesterday_exterior_today_interior`); E3 invariant core
   (`undifferentiated_uncaptured` — stronger than non-fixedness: outside the whole image);
   capstone `exterior_decomposition`; **E4 finite shadow** `height_axis_one_way`
   (`coverTower` on Bool self-covers: no stage carries its own diagonal classifier, the
   next stage does definitionally, the master-classifier wall re-occurs at every height —
   `no_walls_seminar` R7's one-way height axis, cover-shape form, no arithmetization).
3. **The extension protocol** (candidate archetype **A8 EXTEND**, `frontiers/
   exterior_as_extension.md` §5): P1 localize wall as a *named residue* → P2 tetrachotomy
   triage (`∅/0/1/many`) → P3 reify the witness as data → P4 falsifiability gate
   (extension ≠ axiom) → P5 narrow (calibrated negatives are wins) → P6 fate diagnosis +
   **P6′ extension-family cap theorem**.  V3 (Markov retro-diction): **PASS** — the
   G191→G206 arc instantiates every step; amendments P1-generalization + P6′ extracted.

## The V1 payoff — ζ(3) numerator wall re-opened

- **The "no clean WZ certificate" wall is a CAP, not a wall** (P6′ for the `b`-only
  certificate language).  Probe found + verified exact (`zeta3_wz/verify_c_increments.py`,
  Fractions, `n<20`): **the c-increment collapsing laws** — both increments of
  `c(n,k) = H₃(n)+κ(n,k)` are rational multiples of the half-weight carrier
  `√b = C(n,k)C(n+k,k)`: `Δₙc = (−1)^k·w/(n²(n−k))` (k=0 gives `1/n³` — one law unifies
  the H₃/K split), `Δₖc = (−1)^{k−1}·w/(2k³)`, `w=1/√b`.  Δ-calculus on `b·c` is fully
  rational over `(b,√b)`; the A/K-recurrence certificate search moves to
  `span{rational·b·c, rational·√b}`.
- **Round 2 landed (`NumberTheory/AperyCollapsing.lean`, 6 PURE):** `sqw` (the reified
  carrier), `sqw_shift_n` (two `colrec`s), `sqw_shift_k` (`lowrec`+`choose_succ_mul`),
  `square_split` (`k²+(n+k)(n−k)=n²`), bundle `collapsing_core` — exactly the three
  identities the ℚ-proof of the cross-`n` law reduces to (induction step = two lines).
- propext-trap re-confirmed live: core `Nat.add_sub_cancel{,_left}`/`Nat.add_right_comm`
  leak `propext`; NatHelper `add_sub_cancel_right` + `ring_nat` are the pure forms.

## Environment note (next session will hit this)
The session-start hook's elan install **fails silently**: the proxy scopes github.com to
the session repo (403 on release assets), and `releases.lean-lang.org` 302-redirects to
github.com.  Workaround used: **Nix binary cache** — install nix manually
(`releases.nixos.org/nix/nix-2.24.14/...`, `nix-store --load-db`), then
`nix-store -r /nix/store/i9l687hfbmcs45xxy26m22j4ddsrlgnr-lean4-4.16.0`
(Hydra build 290412171, exactly the pinned toolchain) with
`NIX_SSL_CERT_FILE=/root/.ccr/ca-bundle.crt`, substituter `https://cache.nixos.org`.
Then `PATH=/nix/store/i9l687...-lean4-4.16.0/bin:$PATH`.  Consider adding this fallback
to `.claude/hooks/session-start.sh`.

## Open Problems (Priority Order)

### 1. ζ(3) numerator — round 4: Lean-verify THE CERTIFICATE (found 2026-07-02!)
**The numerator certificate is FOUND + verified exact** (`j<26`,
`zeta3_wz/derive_numerator_certificate.py`; plan §"THE NUMERATOR CERTIFICATE"):
`ψ(j,k) = −(−1)^k·k(2j+3)·P₄(j,k)·√b/((j+1)(j+2)²(j−k+1)(j+k+1)(j+k+2))` telescopes the
residual `U = (−1)^k√b·u` (u explicit rational) after the top-row decomposition
(collapsing laws) + Abel with the denominator `Ĝ`; one 3-term boundary identity at
`k=j`.  The old "hand-derived kernel telescoping, hardest piece" verdict is
**overturned** — the route is now denominator-shaped certificate verification.
Lean targets, in order: (a) cleared collapsing laws (on the `AperyCollapsing` bricks);
(b) contiguity reductions of `u`'s four pieces + `T1`'s two; **(c) DONE — R-NUM + R-BND
are PURE** (`NumberTheory/AperyNumeratorWZ.lean`, 13 PURE; R-NUM needed a
machine-generated split: six per-term expansion lemmas + a pairwise collection chain,
since the single `ring_nat` exceeds the reflective normalizer's budget — reusable
pattern); (d) `sumTo` telescoping + R-NIL + the `W`-factoring welds tying R-NUM to the
actual binomial sums; (e) induct `zeta3Num = (n!)³·A`.

### 3. E1 — the connecting maps (`∂²=0` seam)
Stage inclusions for the re-entry tower; `CapturedAt` decomposition as a theorem.
Carried from `the_one_act.md`; design session.

### 4. R7 weld
`height_axis_one_way` ↔ the height-`h` free-parameter fiber-order (no_walls seminar):
is one-way-ness the `q=±1` escape/converge asymmetry on the strength axis, or new?

### 5. V2 (RH) — the method's own falsifier
Protocol predicts P2 lands on `0`.  If a run claims progress, that indicts the method.

## Three-tier state
- **New frontier note:** `research-notes/frontiers/exterior_as_extension.md` (conjecture
  examination + E-series status + protocol P1–P6′ + V-series log).  INDEX registered.
- **Cross-refs updated:** `no_walls_seminar/INDEX.md` (R7 height-axis update),
  `zeta3_wz/numerator_plan.md` (§RE-READ + round-2 landing).
- **Promotion candidates:** none yet — `ExteriorAsExtension` + `AperyCollapsing` are
  fresh; promote the exterior-as-extension arc to `theory/` once E1 closes (the tower
  chapter would then be categorically complete per PROMOTION_CRITERIA).

## File Map
```
NEW (Lean, all PURE):
  lean/E213/Lib/Math/Foundations/ExteriorAsExtension.lean  ← E2/E3/capstone + E4 (15/0)
  lean/E213/Lib/Math/NumberTheory/AperyCollapsing.lean     ← collapsing algebraic core (6/0)
NEW (notes/tools):
  research-notes/frontiers/exterior_as_extension.md        ← the arc's frontier note
  research-notes/frontiers/zeta3_wz/verify_c_increments.py ← exact verification of the laws
MODIFIED:
  lean/E213/Lib/Math.lean                                  ← 2 aggregator imports
  research-notes/frontiers/INDEX.md                        ← entry + status
  research-notes/frontiers/no_walls_seminar/INDEX.md       ← R7 cross-ref
  research-notes/frontiers/zeta3_wz/numerator_plan.md      ← RE-READ + round-2 landing
```
