# ζ(3) nucleus — Apéry's recurrence for `Bₙ` (the WZ identity)

The single remaining nucleus of the ζ(3) `zeta3HolonomicReal` program (see
`../zeta3_blueprint.md` "THE NUCLEUS").  Everything else — Brick 1 (lcm race),
Brick 2 (KeyDiv + Heart + engines), the `c n` integrality input — is PURE-landed.

## The target (Lean anchor: `lean/E213/Lib/Math/NumberTheory/AperyRecurrence.lean`)

`B(n) = Σ_{k=0}^n C(n,k)²·C(n+k,k)²`  (binomial Apéry numbers, manifestly `ℕ`).

> **`(j+2)³·B(j+2) + (j+1)³·B(j) = aperyLead(j)·B(j+1)`**,  `aperyLead j = 34j³+153j²+231j+117`.

Once proven `∀ j`, `zeta3Den n = (n!)³·B(n)` follows by induction (seeds
`B0=1, B1=5` match), closing the recurrence-divisibility route.

## Verified facts (run `python3 verify_recurrence.py`)

  * `B = [1, 5, 73, 1445, 33001, 819005, …]`; the recurrence holds (checked `j≤5`).
  * **The WZ combination sums to zero**: with
    `F(j,k) := (j+2)³b(j+2,k) + (j+1)³b(j,k) − aperyLead(j)b(j+1,k)`,
    `b(n,k)=C(n,k)²C(n+k,k)²`, one has `Σ_k F(j,k) = 0` (checked `j≤6`).  So `F`
    telescopes: `F(j,k) = G(j,k) − G(j,k−1)` for a certificate `G`.
  * `F(j,k) = R_F(j,k)·b(j,k)` with the **exact** rational reduction
    ```
    R_F = -4(2j+3)·P₆(j,k) / [ (j-k+1)²(j-k+2)² ]
    P₆  = 4j⁶+36j⁵−10j⁴k²+7j⁴k+133j⁴−60j³k²+42j³k+258j³
          +4j²k⁴−10j²k³−130j²k²+93j²k+277j²+12jk⁴−30jk³−120jk²+90jk+156j
          +9k⁴−23k³−39k²+32k+36
    ```
    (the term ratios are `b(j+1,k)/b(j,k) = (j+k+1)²/(j+1-k)²`,
    `b(j+2,k)/b(j,k) = ((j+k+1)(j+k+2))²/((j+1-k)(j+2-k))²`,
    `b(j,k-1)/b(j,k) = k⁴/((j-k+1)²(j+k)²)`).

## The remaining sub-problem (immediate next step)

Find the Gosper certificate `cert(j,k)` (rational) with
`G(j,k) = cert(j,k)·b(j,k)` and `F(j,k) = G(j,k) − G(j,k−1)`.  Equivalently solve
the Gosper equation `cert(k) − cert(k−1)·k⁴/((j-k+1)²(j+k)²) = R_F`.

**CAS status**: `sympy 1.14` `gosper_term` returns `None`/hangs on the binomial
form (it mishandles the `j`-shifted binomials and `expand_func` → Γ).  The
certificate *exists* (Σ F = 0).  The Gosper-Petkovšek obstruction is the sextic
`P₆`: at shift `h=j` the numerator/denominator share `(j+k+1)²`, so the GP peel is
non-trivial → the certificate is **high-degree** (this is why the naïve ansatz
spaces and `gosper_term` failed).  Next attempt: implement Gosper-Petkovšek by
hand peeling `h=j` (or sample `cert` at many numeric `j` via a numeric Gosper that
avoids symbolic `cancel`, then interpolate the `j`-dependence).

## Then the Lean formalization (the marathon)

With `cert` in hand, the ∅-axiom Lean proof is: (1) the **summand identity**
`(j+2)³b(j+2,k)+(j+1)³b(j,k) + [neg part of G] = aperyLead(j)b(j+1,k) + [pos part]`
as a Nat additive identity (clear all binomials to factorials à la
`AperyIntegrality.aperyTrinomial`, `ring_nat`) — large, the sextic certificate
makes this the bulk; (2) sum over `k` with `sumTo`, telescoping `G` to boundary
terms; (3) boundary vanishing (`C(n,k)=0` for `k>n`); (4) induction
`zeta3Den n = (n!)³·B(n)`.  Estimate: a dedicated multi-session effort.
