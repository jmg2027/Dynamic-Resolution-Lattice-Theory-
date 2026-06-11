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

## Lean formalization plan (next marathon)

1. `master_identity` — per-coefficient list statement; double recursion
   (`n` outer via the AP/BP recursion, `N` inner with constant factor
   `2N(2N+1)`); signed → split odd/even `n` in subtraction-free pairs.
   Hooks: `AP/BP`, `nth` (LambertOrder), absorption is `ring_nat`-trivial.
2. `halving` — list induction on the AP/BP recursion (or from the closed forms).
3. `flip_dominance` — assemble 1+2 into
   `(4i+2)!!·q^{2i} ≤ R_{2i+1}(i) + (4i+1)!!·q^{2(i−1)}`-form (subtraction-free),
   then `LowerBase` for `q ≥ 1`.
4. (Independent brick) `weld_casoratian` — Discovery 1; hooks `tcross_id`,
   `cf_det_even_nat`; gives the flip criterion + ratio descent as corollaries.
5. `LowerBase` ⟹ instantiate `cothSeriesCauchySepOfBase` + `weld_limit_agreement`
   unconditionally — **the weld closes**.

Provenance: two independent derivation agents converged on §2 (one via Bessel
polynomial / Hermite remainder theory, one via enumerative identity hunting);
all load-bearing claims re-verified by exact computation in this session.
The classical content is the Padé remainder of the Lambert CF; the finite,
subtraction-free reorganization (t-basis positivity, dominance with 10× slack)
appears to be new.
