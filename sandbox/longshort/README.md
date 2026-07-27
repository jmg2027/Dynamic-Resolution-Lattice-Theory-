# Long/short, twice — one asset, then fifty-six

Two studies sharing one stack. Both end negative, and the way each one gets
there is the point.

Unrelated to the DRLT/213 work in the rest of this repository — a standalone
sandbox. Data is daily closes from Yahoo: SPY/^VIX/^IRX back to 1993, and 56
ETFs back to 1996.

| | [**part one — SPY**](spy/README.md) | [**part two — cross-section**](xsec/README.md) |
|---|---|---|
| Universe | 1 index | 56 ETFs, causal entry |
| Net Sharpe | +0.089 | +0.402 full sample, **+0.03 post-2010** |
| Gross Sharpe | +0.152 | +0.717 |
| Placebo `p` | 0.19 | 0.010 |
| Verdict | can't tell — underpowered | powered, and the edge expired in 2010 |

## The stack

Six layers, in `common/`, shared by both studies.

| Layer | What it does |
|---|---|
| **PIT** (`pit.py`) | Probability integral transform, used in *both* directions: forward to put every signal on one distribution-free ruler, inverse to push realised returns back through the predictive CDF as a KS specification test |
| **Edge** (`edge.py`) | Causal expanding estimation with **minimax soft-thresholding** — an adversary picks the parameter anywhere in the confidence interval and we bet against the worst member, so an expert with no statistical support contributes exactly zero rather than noise |
| **Kelly** (`edge.py`) | `f* = μ/σ²`, the log-optimal fraction |
| **Game** (`game.py`) | Hedge / multiplicative weights over the expert pool. Treat the market as an adversary that knows your algorithm: "which expert is right?" becomes unanswerable, but `O(√(T log N))` regret against the best expert in hindsight is available, distribution-free |
| **Execution** (`execution.py`) | No-trade band solved from a cost-aware objective, `w = λc/(hσ²)`, with `λ` **measured** from the book rather than assumed. No free parameter |
| **Audit** (`stats.py`) | Stationary bootstrap, White's Reality Check, deflated Sharpe, PIT calibration, and a placebo that re-runs the entire procedure against returns it cannot predict |

## What each study found

**Part one (SPY).** Ten conventional daily signals on the most arbitraged
instrument in the world produce a gross edge of ~1%/year, smaller than the cost
of harvesting it. The placebo — the same pipeline run 300 times on block-permuted
returns — clears +0.44 five percent of the time, so the observed +0.09 sits at
`p = 0.19`. The real diagnosis is arithmetic: at that effect size, `t = 2`
requires **505 years** of daily data. The experiment was never going to resolve
anything.

**Part two (cross-section).** `IR ≈ IC·√breadth` says the only lever that moves
the exponent is the number of independent bets. It worked: gross Sharpe rose
4.7× (against a `√56 = 7.5` ceiling — about 63% of the law's promise, the
shortfall being correlated country funds), and the detection floor fell from
0.44 to 0.32. The experiment became properly powered, resolved an effect, and
the effect turned out to be **stale international ETF prices**, which expired
around 2010. The 16.5-year modern holdout gives Sharpe +0.03.

## The two findings that generalise

**1. No statistical test asks whether you could have traded it.** The
cross-sectional book executed at the *same close* the signal was computed from
returns Sharpe **+1.77**, and every test endorses it — bootstrap `P(SR≤0)=0.000`,
Reality Check `p=0.000`, deflated Sharpe **1.000** at 200 trials, placebo far
outside the null. A one-day execution lag takes it to +0.40 and two days to
−0.22. The whole thing was a clock, not an edge: EWJ's closing print reflects a
Tokyo session that ended before New York opened. The three-line lag test was
worth more than the other four tests combined, because they all ask whether a
return series is distinguishable from noise and none asks whether it was
ownable.

**2. A no-regret guarantee is not an edge.** Hedge did exactly what it promises
in both studies — found the good expert unsupervised, defunded the dead ones,
kept realised regret well inside `√(T log N/2)`. In part one it still
underperformed naive equal weighting. The guarantee is against an adversarial
world; markets are noisy rather than adversarial, and in that world the
insurance premium is real and payable.

Two supporting results worth keeping: the **execution band** (derived, not
tuned) improved Sharpe, drawdown and turnover simultaneously in both studies and
for every expert individually — the single most robust thing here; and the **PIT
calibration test** independently detected the equity risk premium that part one
deliberately excluded by dropping the regression intercept, without being told
to look for it.

## Three bugs that produced confident wrong answers

Documented in full in [`xsec/README.md`](xsec/README.md), because being clear
about how a plausible number got manufactured is more useful than the number.

1. **Hedge's gain scale hardcoded** → the `[0,1]` clip saturated 47% of the
   time → the exponential weights stopped seeing magnitude → Hedge became a
   hit-rate contest and put **97% of the book on the worst expert**.
2. **Caps binding on 100% of days** → the "Kelly-sized, Hedge-blended" book was
   a sign function times a constant, and nothing downstream was an optimum of
   anything.
3. **Learning from a payoff you don't earn** → with a one-day execution lag the
   estimation layer still fitted on *unlagged* returns: a one-day lookahead, in
   a pipeline written to be paranoid about lookahead, worth 0.44 Sharpe.

## Layout

```
common/     pit · edge · game · execution · stats     the shared stack
spy/        features · backtest · plots · README      part one
xsec/       universe · features · backtest · plots · README   part two
*/out/      results.json · report.png · report.txt    committed outputs
*/data/     vendor CSVs (gitignored, refetchable)
```

## Running it

```bash
pip install numpy pandas scipy matplotlib
cd sandbox/longshort

python3 -m spy.fetch_data && python3 -m spy.backtest && python3 -m spy.plots
python3 -m xsec.universe  && python3 -m xsec.backtest && python3 -m xsec.plots
```

SPY takes ~90s, the cross-section ~20 minutes (200 placebo runs of the full
pipeline). Set `placebo_draws=0` in either `Config` to skip the slow part.

## Timing contract

Identical in both studies: `pos[t]` is decided at the close of day `t` from data
stamped `≤ t`, and earns the return from close `t+lag` to `t+lag+1`. Every
input — PIT quantiles, regression estimates, EWMA volatility, Hedge weights,
holding horizons — respects it. The regression at `t` sums pairs observable by
`t`, which with an execution lag `L` means `s ≤ t−1−L`, not `s ≤ t−1`; getting
that wrong was bug 3.
