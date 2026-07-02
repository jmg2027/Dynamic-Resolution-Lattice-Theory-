# Session Handoff — 2026-07-02 (session 2)

## Branch
`claude/repo-research-context-handoff-vv7z39` — NOT merged.  Continues (fast-forwarded
from) `claude/repo-research-context-3utd48`.  New commits this session:
`f73bff5` (round 4(b) complete), `1bedac8` (round 4(a) algebra core), + plan/handoff.
`lake build` clean; `AperyCollapsing` **18/0 PURE** (`scan_axioms.py`).

## Headline — ζ(3) numerator certificate: rounds 4(b) and 4(a)-core CLOSED

The certificate-verification route (`numerator_plan.md` §"THE NUMERATOR CERTIFICATE")
advanced two steps.  Status of the Lean order (a)–(e):

- **(a) algebra core DONE** (`AperyCollapsing` §4): `collapsing_step` — the `m = k+1`
  kernel-increment step of the ℚ-induction proving collapsing law (1), cleared over
  the carrier triple `√b(n,k)√b(n,k+1)√b(n−1,k+1)`, additive (`n = k+e+1`), with
  `sqw_shift_k_add`/`sqw_shift_n_add` (subtraction-free contiguities).  Remaining in
  (a): the representation layer (see Round-5 blueprint below).
- **(b) DONE** (`AperyCollapsing` §2–§3): `gb_weld` (u-piece 4 — the `Ĝ`-piece's
  crossed reduction against `√b(j,k)`, via `G1a`+`G1b`+`colA`+`colC`);
  `t1_aL_weld` (rides `aperyLead j = (2j+3)(17j²+51j+39)`), `t1_ghat_weld` — `T1`'s
  two `k = j+1` boundary evaluations; `choose_succ_self_right` (`C(j+2,j+1) = j+2`).
- **(c) DONE** (previous session): R-NUM + R-BND PURE (`AperyNumeratorWZ`, 13/0).
- **(d)(e) open** — the mechanical frontier.

**Proof-engineering lesson (recorded in plan):** the first `collapsing_step` attempt
multiplied by `(k+1)⁴(2k+e+2)` → deg-9 `ring_nat` expansions → build timeout (>10 min).
Choosing the mixed `√b(n,k)√b(n,k+1)`-basis with multiplier `(k+1)²(2k+e+2)` keeps
every `ring_nat` ≤ deg 7 and the module builds in ~4 min.  Basis choice controls the
normalizer budget; check the degree before writing the calc.

## Round-5 blueprint (next session's main work) — the representation layer

Canonical: `numerator_plan.md` §"Round-5 blueprint".  Key design points:
1. **Kernel term** `kt N n k m` with `kt_mul_eq` (÷-free deposit), Nat by `heart_lcm`
   (the `2`s of `2m³` and `2lcm³` cancel).
2. **Parity-relative pair** `(A,B)` — `A n (k+1) = B n k + kt …(k+1)`, `B n (k+1) = A n k`
   — gives **uniformly** `(−1)^k·κ(n,k) ~ B_k − A_k`, no parity conditionals.
3. Cleared law (1) = two ℕ-statements (`k = 2t`/`2t+1`), induction step =
   `collapsing_step`, harmonic part = `HL_step`/`cube_dvd_lcm_cube`, base = `sqw_zero`.
4. Then (d): cleared `U` + `sumTo_shift_eq` + `rnum_reduced`/`rbnd_reduced`/`t1_*_weld`
   + R-NIL (`choose_eq_zero_of_lt`) close `ΣU = 0`; (e) 2-step induction à la
   `zeta3Den_eq`.

All new welds were derived + grid-verified numerically FIRST
(scratchpad scripts; the exact statements are in the theorem docstrings) — keep this
verify-then-deposit discipline.

## Environment note
The session-start hook's elan install worked this session (`/root/.elan/bin/lake`
present).  If it fails, see the previous handoff's Nix binary-cache workaround
(preserved in git history at `36afdde`, HANDOFF.md §"Environment note").

## Open Problems (Priority Order)

### 1. ζ(3) numerator — round 5: the representation layer + ΣU = 0
Blueprint above; all algebra bricks now PURE.  This is representation design +
divisibility plumbing (heart_lcm applications), not new mathematics.

### 2. E1 — the connecting maps (`∂²=0` seam)
Stage inclusions for the re-entry tower; `CapturedAt` decomposition as a theorem.
Carried from `the_one_act.md`; design session.

### 3. R7 weld
`height_axis_one_way` ↔ the height-`h` free-parameter fiber-order (no_walls seminar):
is one-way-ness the `q=±1` escape/converge asymmetry on the strength axis, or new?

### 4. V2 (RH) — the method's own falsifier
Protocol predicts P2 lands on `0`.  If a run claims progress, that indicts the method.

## Three-tier state
- `research-notes/frontiers/zeta3_wz/numerator_plan.md` — round-4 statuses + round-5
  blueprint updated (this is the working document).
- `research-notes/frontiers/exterior_as_extension.md` — unchanged this session.
- **Promotion candidates:** none new — `AperyCollapsing`/`AperyNumeratorWZ` promote to
  `theory/` together once the ζ(3) numerator arc closes; the exterior-as-extension arc
  waits on E1.

## File Map
```
MODIFIED (Lean):
  lean/E213/Lib/Math/NumberTheory/AperyCollapsing.lean  ← §2 +gb_weld, §3 T1 welds,
                                                          §4 collapsing_step (18/0)
MODIFIED (notes):
  research-notes/frontiers/zeta3_wz/numerator_plan.md   ← (a)(b) statuses + round-5
  HANDOFF.md                                            ← this file
```
