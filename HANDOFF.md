# Session Handoff — 2026-06-11 (THE WELD CLOSES: `LowerBase` proven, coth series ≡ CF unconditional)

## Branch & build state
`claude/weighted-ibp-li-yau-91qefg`.  `lake build` ✓ clean (run from `lean/`!);
`scan_all_axioms.py` **2415 PURE / 0 DIRTY** (+33 sealed-DIRTY-by-design).
Session module: `Real213/ExpLog/LambertBridge.lean` **77 PURE / 0 DIRTY**.

## What was done — `lowerbase_blueprint.md` F1–F7, executed to the end

The weld's one remaining brick — `LambertOrder.LowerBase`
(`∀ i, devA_i·s_{2i+1} ≤ (4i+3)·devB_i·c_{2i+1}`) — is now a theorem:
`LambertBridge.lowerBase (q) (hq : 1 ≤ q) : LowerBase q`.  Consequences,
both ∅-axiom and hypothesis-free:

  * `cothSeriesCauchySep q hq : CauchyCutSeq` — the `coth(1/q)` series fold
    completes, total modulus `k+2`;
  * `weld_closed q hq m k` — the series and CF limit cuts agree on **every**
    probe: the two pointings of `coth(1/q)` are one.

### The proof, layer by layer (all in `LambertBridge.lean`)
1. **§1–§4 (F1)** reversal infra + `rev_trunc`: `rev (AP (2i+1)) = truncA (2i+1) i`
   (4-way joint induction over the parity ladder) — the reversed convergent
   lists ARE the coefficient stacks.
2. **§5 (F2)** `wprod` (threaded weight) + `Aacc/Bacc` snoc (last-step peel,
   `wprod_shift` aligning head-peel with weight threading).
3. **§6–§7 (F3)** σ/γ-steps, `prod_match`(+`_B`), `wmatchA/B`, and the
   **bridges**: `Mf(g)·(stack ⋆ σ/γ)_p + Acc(g) = Acc(p+g+1)` — induction on
   `p` at fixed `g`, `N̂ = J+g` invariant.
4. **§8 (F4)** `budgetGen`: `(2J+2)·Bacc ≤ w·wprod·(2·bpF n s)` whenever
   `2J+1+2·steps ≤ cc` — the division-free budget (uses `bpF_halving`).
5. **§9 (F5a)** saturation: `AaccSum/BaccSum (2i+1) N (i+1) = Asum/Bsum`,
   **every** `N` (support vanishing `apF/bpF_vanish_ge` ∨ weight vanishing
   `wprod_vanish`, whichever first).
6. **§10 (F5b)** mirrors: `sig_eq_wprod`, `gam_eq`, `wprod_split`, and
   `mirrorA/B`: past the stack, the coefficient = `wprod (2J+1) r ·`
   (saturated accumulator at level `K = J−r`).
7. **§11 (F5c)** per-coefficient laws of the two `LowerBase` lists `LAl/LBl`
   (both length `3i+2`): `entry_eq` (equal past the diagonal — `cfpos` vanishes
   below the level, the master identity is an equality), `diag`
   (`LB_i = LA_i + cfpos n n`, the `(4i+2)!!` Padé flip), `slack`
   (`(2n+2)·LA_p ≤ (2n+2)·LB_p + 2·bpF n 0` below it — budget, `wprod`-cancelled).
8. **§12 (F6)** assembly: `suffix_peel`, `sufEq` (suffix equality past the
   diagonal), `cfpos_diag_rec` + `bpF_le_cfpos` (`(4i+1)!! ≤ (4i+2)!!`,
   counting), `inv_descent` (the descent invariant), `suffdom_LAl` — the
   diagonal flip absorbs the ≤ `i` slack quanta (`2i·(4i+1)!! ≤ (4i+4)·(4i+2)!!`).
9. **§13 (F7)** `suffdom_general` + `lowerbase_len` → `lowerBase` → the weld.

### Lean tactics intel (recurring pitfalls, this session)
* `Nat.le.dest` on `a < b` yields `Nat.succ a + k = b`; **`ring_nat` treats
  `Nat.succ a` as an opaque atom** (≠ `a + 1`) — convert via `congrArg (· + 1)`
  / `Nat.succ_add` instead of `rw [← he]; ring_nat`.
* PolyNatM does **not** cancel zero monomials: goals containing `+ 0` or
  `1 * _` make `poly_idM` norms differ — eliminate the literals first
  (`Nat.zero_mul`/`Nat.one_mul`/`Nat.zero_add` rws, or route junk terms
  through `Nat.le_add_right` and feed `ring_nat` the clean equality).
* `rw` finishes goals like `[].length + (1+1) = 2` only up to reducible —
  append explicit `rfl`.

## Weld arc status (the whole picture)
* `exp(2/q)` headline: **closed** earlier via `ExpMoebius` (independent route).
* `coth(1/q)` series ≡ CF: **closed this session** (above).
* Open neighbours (frontiers): exp(p/q) free modulus (`exp_pq_no_htel`
  boundary), CothSeriesCut 3c ∀-probe order transfer (superseded for
  `coth(1/q)` by `weld_closed` — check if anything残 references it),
  ζ(3) bricks (`zeta3_blueprint.md`, `zeta3_free_modulus.md` — verified
  blueprints, not yet formalized).

## Next candidates
1. **Promotion**: the Lambert weld sub-tree (Weld/Minor/Order/MasterId/Poly/
   Bridge) is now closed — check `theory/PROMOTION_CRITERIA.md` H1–H4 + S1–S3,
   write the `theory/` mirror chapter, archive the scratch notes.
2. ζ(3) formalization marathon (two verified blueprints waiting).
3. `weld_casoratian` (§9 LambertOrder) — the exact `i`-invariant identity,
   an independent certificate brick.
