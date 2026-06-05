# Session Handoff — 2026-06-05 (transcendentals T1–T3/T5 + PDE P1–P3 marathon)

## Branch
`claude/transcendentals-pde-marathon-93F1Y` — all work pushed.  `cd lean && lake build` clean on every
touched module + `Analysis.ODE` aggregator.  Autonomous marathon (invoke `autonomous-research` to continue).

## The arc
Two genuinely-hard blocks split off the A6 Ricci core into standalone ladders; this marathon drove them far,
**all strict ∅-axiom** (`#print axioms` empty on every theorem below).  Then a `choose`↔factorial bridge
opened the exp functional-equation / combinatorics front (T5).

## State by rung

### Transcendentals (`research-notes/frontiers/transcendentals/transcendental_functions_ladder.md`)
- **T1 ✅** exp Taylor convergence modulus (ratio-test core) — `ExpLog/CutExpModulus.lean`: geometric
  majorant `Mⁿ/n!`, term decay `≤ term(2M)·2^{−j}`, antitone.  + `ExpLog/CutExpConvergents.lean`: exp(m)
  rational convergents, `exp_cross_det`, route-unification (`exp_increment_eq_taylor`,
  `exp_increment_geom_decay`).  **Honest finding**: e's clean `N=k+2` modulus is m=1-special.
- **T2 ✅** sin/cos convergence by comparison — `ExpLog/CutTrigModulus.lean` (geom decay + antitone).
- **T3 ✅** formal derivative rules (coefficient level): `exp_deriv_coeff_fixed`, `sin_deriv_coeff`,
  `cos_deriv_coeff` — all from one factorial shift `(n+1)·n! = (n+1)!`.
- **T5 (partial)** `choose`↔factorial bridge `choose_mul_factorials` (`C(k+j,k)·k!·j! = (k+j)!`),
  `choose_symm`, `pascal_row_sum` (`Σ C(n,k)=2ⁿ`), `choose_le_two_pow` (`C(n,k)≤2ⁿ`) — in
  `NumberTheory/DyadicFSM/FLT/{ChooseFactorial,BinomialTheorem}.lean`.  b=1 binomial `(a+1)ⁿ=ΣC(n,k)aᵏ`
  already PURE (`binom_theorem_b_eq_one`).
- **T4** sqrt — NOT started (rich `Analysis/DyadicSearch/IVT`+`RootCertificate`+`MinimalRootLens` infra
  exists; `Sqrt2Cut` is Pell-only).

### PDE estimates (`research-notes/frontiers/pde_estimates/discrete_pde_estimates_ladder.md`)
- **P1 ✅** maximum principle — `Analysis/ODE/HeatEqDiscrete.lean`: per-step/iterated/strong-strict +
  comparison principle (`heatStep_mono`, the max principle re-derived as comparison vs a constant).
- **P2 ✅** the non-lazy `(½,0,½)` step does NOT decay oscillation (checkerboard `−1` eigenmode);
  the lazy `(¼,½,¼)` `lazyHeatStepNum` is the smoothing operator (witness `lazy_checker_collapses`).
- **P3 ✅ (capstone)** — `HeatEqConservation.lean` (gridSum infra + mass conservation + Dirichlet pairing +
  signed energy `dirichletEnergy` + Green identity `E+2corr=2Σu²`), `HeatEqEnergyL2.lean` (L²-Jensen +
  local dissipation), `HeatEqEnergyDecay.lean` (**`lazy_energy_decay`: `E(lazy u) ≤ 16·E(u)`**, the
  energy-method conclusion — `Nat`↔ℤ bridge `sqDistNat_cast` + `Int213.Order.le_of_ofNat_le` + shift inv).
- **P4/P5** Li–Yau / Shi — NOT started (the "real analytic depth", may stall).

## Reusable infra built
`gridSum` (`HeatEqConservation`): `gridSum_congr/_add/_mul_left/_two_mul/_le`, cyclic-shift invariance
(`gridSum_rightNbr/_leftNbr` via `leftNbr_rightNbr`), `sqDistNat` + `sqDistNat_cast`.  `sumTo_term_le`.

## ∅-axiom hazards discovered (use the pure replacements)
Core leaks `propext`: `Nat.mul_assoc`, `Nat.add_sub_cancel`/`add_sub_cancel_left`, `Nat.sub_eq_zero_of_le`,
`Nat.add_mod_right`, `Int.ofNat_le`(.mp), `Int.ofNat_sub`, `Nat.sub_ne_zero_of_lt`, `Nat.sub_pos_of_lt`.
`funext`/`ac_rfl`/`simp`-AC/`omega` leak `propext`/`Quot.sound`.  Pure substitutes: NatHelper
`mul_assoc`/`add_sub_cancel_right`/`add_sub_add_left`/`sub_one_add_one`, AddMod213 `mod_self`,
`Int213.Order.le_of_ofNat_le`/`ofNat_sub_ofNat`+`subNatNat_of_le`, `Nat.zero_sub`, term-mode `Int.ofNat`
casts (explicit-`Int.ofNat`-typed `have`s dodge the `Nat.cast` rw-mismatch), `ring_nat`/`ring_intZ`
(but prune literal `0*0` zero-coefficient terms first — the normalizer doesn't drop them).

## Next targets
1. **T5 general 2-var binomial** `(a+b)ⁿ = Σ_{k≤n} C(n,k) aᵏ bⁿ⁻ᵏ` — the remaining T5 core.  Proof sketch
   (mirror the b=1 `binomSum_step`): define `binomSum2 a b n = sumTo (n+1) (fun k => choose n k * a^k * b^(n-k))`;
   prove `binomSum2_step : (a+b)*binomSum2 a b n = binomSum2 a b (n+1)`, then induct.  Step = show
   `binomSum2 a b (n+1) = A + B` where `A = a*binomSum2 = sumTo(n+1)(C n k · a^{k+1} · b^{n-k})`,
   `B = b*binomSum2 = sumTo(n+1)(C n k · a^k · b^{n-k+1})`.  Both reduce to
   `b^{n+1} + A + thirdterm` (`thirdterm = sumTo(n+1)(C n (k+1) · a^{k+1} · b^{n-k})`): RHS via
   `sumTo_split_first` (k=0 → b^{n+1}) + Pascal `choose_succ_succ` + `sumTo_add_func`; `B` via
   `sumTo_split_first` + boundary `choose_eq_zero_of_lt n (n+1)` (drops the last term).  b-exponent
   congruences (`sumTo_congr`): `n+1-(k+1)=n-k` (`Nat.succ_sub_succ`, pure), `n-(k+1)+1=n-k` for k<n
   (`NatHelper.sub_one_add_one` + a *pure* `n-k≠0` from `NatHelper.sub_pos_of_lt`).  **Heavy** (propext
   whack-a-mole on the Nat-sub steps) but fully mapped.  Then exp(a+b)=exp(a)exp(b) at coeff level follows
   via `choose_mul_factorials`.
2. **T4 sqrt** via the existing `DyadicSearch/IVT`/`RootCertificate` infra (bisection + convergence modulus,
   `(sqrtCut a)² = a` up to `cutEq`, `d/dx sqrt`).
3. **Cut-level packaging**: exp/sin/cos as genuine `CauchyCutSeq` points (the T1→T2 rate is done; the
   stabilization needs a generalized-margin RateModulus — *not* a shifted one, the margin is e-tied).
4. **P4 Li–Yau** (may stall — the real analytic depth).

## Tally
12 files, ~68 PURE theorems.  T1–T3 + P1–P3 (capstone) complete; T5 substantially advanced.
