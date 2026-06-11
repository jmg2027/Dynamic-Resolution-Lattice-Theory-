# LowerBase — the verified proof blueprint (multi-agent round, 2026-06-11)

Status: **OPEN in Lean, CLOSED on paper** — every identity and inequality below
was re-verified independently by exact symbolic computation (sympy, general `q`,
ranges noted) after a multi-agent derivation round.  This note is the
formalization blueprint for the weld's last brick
(`LambertOrder.LowerBase`): for all `i`,

    devA_i · s_{2i+1}  ≤  (4i+3) · devB_i · c_{2i+1}

(`devA_i = dev q (AP (2i+1)) = p_{2i}/q`, `devB_i = dev q (BP (2i+1)) = q_{2i}`,
`c/s` the cleared cosh/sinh partials, `R_J(i) := (2J+1)·devB_i·c_J − devA_i·s_J`).

## Discovery 1 — the weld Casoratian (exact, i-invariant)

The pair `(R_J(i), M_J(i))` (`M_J(i) := P_i·s_J − (2J+1)q²·Q_i·c_J ≥ 0` the
(U)-margin, `P_i = p_{2i+1}`, `Q_i = q_{2i+1}/q`) evolves in `i` by a
**unimodular** matrix (`det = 1`), so the cross of two truncations is
`i`-INVARIANT, and it collapses to the proven `tcross_id` quantity:

    R_{J+1}(i)·M_J(i)  =  R_J(i)·M_{J+1}(i) + K_J,
    K_J = (2J+3)·s_J − (2J+1)·c_J          [= the `t_mono` cross, ≥ 2·c_J]

(verified symbolically, all `i ≤ 3`, `J ≤ 3`, general `q`; `K_J ≥ 2c_J` from
`cosh_le_sinh`).  Proof is bilinear expansion + the det-one floor
`P_i·devB_i = q²·devA_i·Q_i + 1` (descended `cf_det_even_nat`): the `cc'`/`ss'`
terms cancel, the cross terms carry coefficient exactly `1`, leaving
`(2J+1)c_J s_{J+1} − (2J+3)c_{J+1}s_J = −K_J` — which is `tcross_id`.
A page of `ring_nat`.  Consequences:

  * **flip criterion**: `K_J > |R_J|·M_{J+1}` forces `R_{J+1} > 0`;
  * **ratio descent**: pre-flip, `|R_J|·M_0 ≤ |R_0|·M_J` (telescoped).

This identity is an independent certificate of the system's exact structure
(and worth a Lean brick of its own), but the shorter proof path is Discovery 2.

## Discovery 2 — the master identity and the dominance route

Coefficient closed forms (`[k]` = `u^k`-coefficient, list position `i−k`;
verified `i ≤ 9`):

    devB_i[k] = (i+k)!·(2i+2k+1)!! / ((i−k)!·(2i−2k+1)!!·(2k)!)
    devA_i[k] = devB_i[k] · (i+k+1)(2i−2k+1)/(2k+1)

**Master identity** (the untruncated Padé remainder, coefficientwise; verified
`n ≤ 15`, `N ≤ 29`): with `w_{N,s} = (2N+1)!/(2N−2s+1)!`,

    Σ_s w_{N,s}·[(2N−2s+1)·B_n[s] − A_n[s]] = (−1)^{n−1}·2^n·N!/(N−n)!   (0 for N < n).

Equivalently `B_n(u)·Σu^j/(2j)! − A_n(u)·Σu^j/(2j+1)!` `= ±Σ_m u^{n+m}/((2m)!!(2n+2m+1)!!)`
— the error tail is an explicit positive series.  PROOF (checked): induction on
`n`; the list recursion `B_{n+2} = (2n+3)B_{n+1} + shift(B_n)` has constant
weight-ratio `w_{N,s+1}/w_{N−1,s} = 2N(2N+1)`, so

    LHS_{n+2}(N) = (2n+3)·LHS_{n+1}(N) + 2N(2N+1)·LHS_n(N−1),

and the RHS satisfies the same recursion by `4(N−n−1) = −2(2n+3) + 2(2N+1)`
(the double-factorial absorption `(2n+2m+5) = (2n+3) + (2m+2)` — the analog of
`binom_absorption`).  Bases `n = 1, 2` are one-liners (`2N`, `−4N(N−1)`).

**Sliver structure** (from unrolling `R_{J+1} = (2J+2)(2J+3)q²R_J + E_{J+1}`,
`E_j := (2j+1)devB_i − devA_i`):

    R_J(i) = Σ_{j=0}^{J} [(2J+1)!/(2j+1)!]·q^{2(J−j)}·E_j .

  * constant term `[q⁰]R_J = 2J+1 − (i+1)(2i+1)` (the arithmetic slivers);
  * top coefficient `[q^{2(i−1)}]R_J = −(4i+1)!!/(2J+3)` for `J ≤ 2i−1`;
  * at `J = 2i` the first error term enters: `−(4i+1)!!/(4i+3) + (4i+1)!/(2(4i+5)!!)`
    (resolves the "odd-ball 51");
  * flip leading coefficient `[q^{2i}]R_{2i+1}(i) = (4i+2)!!` exactly.

**Positivity certificates** (all re-verified, `i ≤ 6–8`):

  1. `E_j ∈ ℕ[t]` for every `j ≥ 1` (`t = q²−1`) — the ONLY negative input is
     `E_0 = devB − devA`;
  2. `R_{2i+1}(i) ∈ ℕ[t]` (e.g. `48t+49`; `3840t²+7755t+3911`;
     `645120t³+1946385t²+1956780t+655502`);
  3. **dominance, t-coefficientwise**: `R_{2i+1}(i) − q^{2(i−1)}·((4i+2)!!·q² − (4i+1)!!) ∈ ℕ[t]`
     — so `LowerBase` follows from the master identity + the bound
     `Σ|C_{i−s}| ≤ (4i+2)!!/(4i+5) + 4·(4i+1)!!·(4i+6)/((4i+4)(4i+5)) < (4i+2)!!`,
     whose inputs are the **halving lemma** `2·A_n[s+1] ≤ A_n[s]`,
     `2·B_n[s+1] ≤ B_n[s]` (verified all `n ≤ 13`; geometric column decay) and
     `(4i+1)!! ≤ (4i+2)!!/2`.  Slack ≥ 10× at every `i` (no exact cancellation
     anywhere on this route — the 1.0098-tight coupling crunch is dissolved);
  4. propagation past the flip is already in Lean (`lower_step`).

Bonus minor closed form (same-level pair, `s < t`, `k = i−position`):
`b_s a_t − a_s b_t = (t−s)·[(2i+1)(2i+2) + (2k_s+1)(2k_t+1)]·devB[k_s]devB[k_t]/((2k_s+1)(2k_t+1))`
— manifestly positive; re-proves `minor_all` with exact values.

## Lean formalization plan (status)

**Backbone formalized** (LambertOrder §10, all PURE):
  * `R_recursion` — `R_{J+1} = (2J+2)(2J+3)q²·R_J + ((2J+3)dB − dA)`,
    subtraction-free, straight from the `coshNum`/`sinhNum` recursions; ✅
  * `E_nonneg` — `dA ≤ (2j+1)dB` for `j ≥ 1` (from `devA_le_three_devB`); ✅
  * `weld_casoratian` — Discovery 1, the `R/M` det-one coupling (LambertOrder §9); ✅
  * `master_diagonal_anchor` — `L(3,3) = 48 = 6!!` machine-checked; ✅
  * `lower_base_anchors` — base verified at `(q,i) = (1,1),(1,2),(2,1),(1,3)`. ✅
  Together with the **already-proven** `lower_of_base` (J-propagation) and
  `devA_le_three_devB` (side condition), this reduces `LowerBase q` to **exactly
  the base family `R_{2i+1}(i) ≥ 0`** — everything downstream
  (`series_ge_even_of_base`, `cothSeriesCauchySepOfBase`, `weld_limit_agreement`)
  is conditional only on it.

**The master identity is now PROVEN** (`LambertMasterId.lean`, 37 PURE):
entirely over `ℕ`, subtraction-free, via the weight-threading accumulators
`Bacc/Aacc` (which carry `cc = 2N−2s+1` and `w = W(N,s)` so the `2N−2s`
subtraction is never formed) — sidestepping the Int/Nat-subtraction friction
the original plan flagged.
  * `master_odd`: `Asum(2k+1,N) + cfpos(2k+1,N) = Bsum(2k+1,N)`;
    `master_even`: `Bsum(2k,N) + cfpos(2k,N) = Asum(2k,N)`;
    `cfpos n N = 2ⁿ·descFac N n` (`= 0` for `N < n`, the Padé cancellation).
  * Engine `cfpos_moved` (`binom_absorption` analog):
    `cfpos(n+2,N) + (2n+3)cfpos(n+1,N) = 2N(2N+1)cfpos(n,N−1)`, via top-peel +
    `descFac_bottom` + `descFac_coeff` (`2(N−1−n)+(2n+3) = 2N+1`).
  * Proof = `master_pair`, a paired two-step induction on `k` carrying the
    `(2k, 2k+1)` block (step = `Bsum/Asum` three-term recursions + `cfpos_moved`).
  * `master_diagonal`: `Bsum(2i+1,2i+1) = Asum(2i+1,2i+1) + cfpos(2i+1,2i+1)`,
    the leading value `(4i+2)!!` (anchors `cfpos 3 3 = 48`, `cfpos 5 5 = 3840`).

**The connection layer is now FORMALIZED** (`LambertPoly.lean`, 26 PURE):
  * `evc` (constant-first evaluation) + `lmulC` (convolution) — length-condition-
    free polynomial layer; `dev_eq_evc_rev` bridges the weld's `dev` world in;
    `cListC/sListC` (coefficient lists of the cleared cosh/sinh partials);
    `conn_A/conn_B`: both `LowerBase` sides are `evc`s of explicit convolutions.
  * **`evc_dom_joint` — the Abel transfer**: equal-length *suffix dominance*
    (every suffix coefficient-sum of `A` ≤ `B`'s) ⟹ `evc q A ≤ evc q B` for all
    `q ≥ 1`, by a joint induction carrying the cross-statement
    `evc q a + evc 1 b ≤ evc q b + evc 1 a` (cons-heads cancel; `q² = 1+e`).
    **This eliminates the `q`-dependence entirely** — the remaining content is a
    `q = 1` statement.
  * `lowerbase_of_suffdom`: `LowerBase` at level `i` ⟸ suffix dominance of the
    two convolution lists.  **End-to-end at `i = 1`**: `lowerbase_one` proves the
    base inequality for *every* `q ≥ 1` through the full pipeline.

**Remaining — ONE brick**: general-`i` suffix dominance at `q = 1`,
`SuffDom (lmulC (rev (AP (2i+1))) (sListC (2i+1)))
        (lmulC (rev (BP (2i+1))) (lsmul (4i+3) (cListC (2i+1))))` —
verified numerically (i ≤ 4).  Structure: suffix sums obey the clean recursion
`Suf k (lmulC (a₀::as) b) = a₀·Suf k b + Suf (k−1) (lmulC as b)` (drop commutes
with ladd); per-grade the difference is `(4i+2)!!` (`master_diagonal`) plus
partial slivers, controlled by the master identity (`LambertMasterId`, proven)
+ halving (`apF/bpF_halving_strong`, proven) at `q = 1`.  Then `LowerBase` ⟹
`cothSeriesCauchySepOfBase` + `weld_limit_agreement` unconditional — **the weld
closes**.  (NB the weld's *headline*, `exp(2/q)` unconditional, is **already
closed** independently via `ExpMoebius`.)

Provenance: two independent derivation agents converged on §2 (one via Bessel
polynomial / Hermite remainder theory, one via enumerative identity hunting);
all load-bearing claims re-verified by exact computation in this session.
The classical content is the Padé remainder of the Lambert CF; the finite,
subtraction-free reorganization (t-basis positivity, dominance with 10× slack)
appears to be new.
