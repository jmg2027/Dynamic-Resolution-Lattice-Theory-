# Decomposition: gcd / the Euclidean algorithm (the residue Lens iterated to its q=+1 fixed point)

*213-decomposition of "gcd / Euclidean algorithm", per `../README.md`.*

This is the **terminating** sibling of `prime_distribution.md` and the **iterate** of
`modular_arithmetic.md`.  The residue Lens `n ↦ n % m` (the count-Lens, `modular_arithmetic.md`), **fed back
into itself**, is the Euclidean algorithm; its **q=+1 fixed point** (the step where the residue hits `0`) is
the gcd.  Where prime distribution is the residue-Lens iteration that *never* terminates (`q=−1`, infinitely
many atoms), the Euclidean descent *always* terminates (`q=+1`, a well-founded modulus strictly decreases).

## The decomposition

- **Construction `C`** — a **pair of counts** `(a, b)`.
- **Reading `L`** — the **Euclidean step** `(a, b) ↦ (b, a % b)`: apply the residue Lens `a ↦ a % b`
  (`modular_arithmetic.md`) and swap.  Verbatim the repo's recursion
  (`Meta/Tactic/NatHelper.lean:618 gcdFuel`):
  ```
     gcdFuel (n+1) (a+1) b  =  gcdFuel n (b % (a+1)) (a+1)      -- residue Lens, then recurse
  ```
- **Fixed point / `⊕`** — iterate `L` until the residue vanishes (`a % b = 0`); the surviving component is
  `gcd a b`.  The **dropped** part is the pair of **coprime cofactors** `a/g, b/g` (the residue complement:
  what gcd forgets — the part of `a, b` *not* common).  The iteration is `q=+1` (terminating): the modulus
  `M(a,b) = max a b + a` **strictly decreases** each step, so the descent is well-founded (fuel
  `2·(a+b)+1` suffices — `gcd213` is total ∅-axiom, no `partial`).

## Re-seeing the theorems

gcd has a **dynamic** and a **static** reading, and they are one object:

- **Dynamic (the algorithm)** — gcd is *computed* as the `q=+1` fixed point of the iterated residue Lens
  (`gcdFuel`).  Termination is the well-founded modulus, the 213 "computable narrowing interval" made
  discrete — it *reaches* its limit (the residue `0`) in finitely many steps, unlike the prime-distribution
  residue which is reached by none.
- **Static (the lattice)** — gcd is the **meet in the divisibility lattice**: `gcd ∣ a`, `gcd ∣ b`
  (`Meta/Nat/Gcd213.lean:149 gcd213_dvd_left`, `:154 gcd213_dvd_right`) and it is the *greatest* such
  (`:264 gcd213_greatest`: `d ∣ a → d ∣ b → d ∣ gcd a b`) — the universal property of a GLB.  And **that
  lattice is the Lens-refinement lattice**: `Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean:122
  leavesModNat_lcm` proves `L_{lcm(m,k)} ≈ prodLens(L_m, L_k)` — "`refines` = `∣`, meet = lcm" — so the
  divisibility lattice gcd/lcm live in *is* the count-Lens refinement lattice, and CRT is its coprime case
  (`gcd = 1`, `lcm = m·k`).

## Revelation (collapse + forcing)

**Collapse — "the Euclidean algorithm" and "gcd = the meet" are one.**  The dynamic recursion and the static
universal property are not two facts joined by a correctness theorem; the algorithm *is* the meet, computed by
driving the residue Lens to its fixed point.  `gcd213_greatest` is the meet; `gcdFuel` is the meet's
computation; they are `⟨C|L⟩` read as process and as property.

**Forcing — gcd (terminate) and prime distribution (never terminate) are the two faces of iterating the
residue Lens.**  One residue-Lens iteration: on a *pair* it descends to `0` (finite, `q=+1` — gcd); on the
*basis of atoms* it never exhausts (infinite, `q=−1` — `exists_prime_gt`, `prime_distribution.md`).  The same
operation (`modular_arithmetic.md`'s `% `, iterated) splits by the standing tag into the converge side (gcd)
and the escape side (the prime sequence).  The descent modulus `M(a,b)` is the well-founded *bracket* that
forces `q=+1`; its absence (no top atom) is what makes the prime side `q=−1`.

## Verified Lean anchors (file:line:theorem — grep-confirmed, scans from repo root this session)

- `Meta/Tactic/NatHelper.lean:618 gcdFuel` — the Euclidean recursion = residue Lens `b % (a+1)` fed back;
  `gcd213` allocates fuel `2·(a+b)+1` (the well-founded `q=+1` descent, modulus `M(a,b)=max a b + a`).
- `Meta/Nat/Gcd213.lean:149 gcd213_dvd_left`, `:154 gcd213_dvd_right` (`gcd ∣ a`, `gcd ∣ b`); `:264
  gcd213_greatest` (the GLB universal property = the divisibility-lattice meet). **PURE (33/0).**
- `Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean:122 leavesModNat_lcm` — the count-Lens refinement
  lattice mirrors divisibility (`refines = ∣`, meet = lcm); CRT = the coprime (`gcd=1`) case. **PURE (4/0).**
- `Meta/Nat/NatDiv213.lean:126 div_add_mod_pure` — the residue Lens step `a = b·(a/b) + a%b` whose iteration
  this is (`modular_arithmetic.md`).
- Dual: `Lens/Number/Nat213/MultSystemValue.lean:689 exists_prime_gt` — the `q=−1` non-terminating face
  (`prime_distribution.md`).

## BUILT vs ABSENT

- **BUILT (∅-axiom):** the algorithm (`gcdFuel`/`gcd213`, total, well-founded), the divisibility-meet
  universal property (`gcd213_greatest`), and the Lens-lattice mirror (`leavesModNat_lcm`, `lcm = meet`,
  CRT coprime case).
- **ABSENT (predicted-not-built):** the **Bézout witness** `gcd a b = a·x − b·y` as a single clean ∅-axiom
  identity (the `ModBezout`/`JoinBezout` files build the Lens-refinement *chain* and `xgcdAux`, but the
  packaged `gcd = combination` integer statement is not isolated); the **continued-fraction bridge** (the
  Euclidean quotients = the CF of `a/b`, `continued_fractions.md` — the same descent read as a real-pointing).

## Touches the model?

**No new primitive — gcd is the count-Lens's own fixed-point operator.**  Both invariants hold: the operation
is the residue Lens (`modular_arithmetic.md`) iterated, and the `q=±1` tag splits its iteration into gcd
(terminate, `+1`) vs the prime sequence (escape, `−1`).  The new datum: gcd unifies the **dynamic** (Euclidean
descent) and **static** (divisibility-lattice meet) readings as one `⟨C|L⟩`, with the lattice *itself* shown to
be the count-Lens refinement lattice (`leavesModNat_lcm`) — completing the residue-Lens triptych
`modular_arithmetic` (the Lens) → `gcd_euclidean` (its terminating iteration) → `prime_distribution` (its
non-terminating iteration).
