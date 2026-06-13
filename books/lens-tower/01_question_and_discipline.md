# Chapter 1 — The Question and the Discipline

## 1.1 The structure that appears

Take the residue's self-pointing — the slash `a/b`, the act of distinguishing — and iterate it.
Read each stage with a determinant of three consecutive readings,

```
D(n) = s(n)·s(n+2) − s(n+1)²,
```

and a rigid structure comes into view. The determinant does not wander: it multiplies by a fixed
factor each step. Consecutive triples lie on a fixed conic. Certain iterations close into
periods — `4` and `6` — while others escape. A sign `±1` rides along, flipping or held constant.
Three numbers organize everything: `−3`, `−4`, `+5`. A point that "should" be there, `−2`, is
missing.

Anyone trained in number theory recognizes this instantly. The orders `{2, 4, 6}` are the unit
groups of the imaginary quadratic rings `ℤ`, `ℤ[i]`, `ℤ[ω]`. The numbers `−3, −4` are their
discriminants; `+5` is the discriminant of the golden field. The periods `4, 6` are the orders
of the elliptic generators `S, U` of the modular group. The sign `±1` is the Pell unit. The
missing `−2` is the discriminant of `ℤ[√−2]`, whose unit group is only `{±1}`.

So the temptation is overwhelming: **213 contains the imaginary quadratic fields and the modular
curve.** And one can make the temptation rigorous — every identity above is `∅`-axiom provable in
Lean. The orders are real (`ImaginaryQuadraticUnitTrichotomy.imaginary_quadratic_unit_trichotomy`),
the determinant law is real (`CassiniUnimodular.det_step`), the modular generator orders are real
(`Real213.ModularElliptic.modular_generator_orders`).

## 1.2 Why the temptation must be resisted

The framework forbids this move at its root. Two rules:

**No exterior** (`seed/AXIOM/05_no_exterior.md` §5.1). There is nothing outside 213 for it to
*correspond to*. A Lens application is itself a residue self-pointing event, not a tool reaching
in from a pre-existing mathematical universe. So "213 corresponds to the imaginary quadratic
fields" is not a theorem the framework can even state without importing the very exterior it
denies.

**Assume nothing, give meaning to nothing** (the meta-principle). Every imported word —
"discriminant," "field," "modular," "genus" — carries residual meaning from outside. The
discipline is to minimize it, acknowledge what cannot be removed, and never *add*. Naming the
structure "the imaginary quadratic units" adds an entire theory's worth of meaning that the
residue never asked for.

The repository names the precise error this risks: **stereotype matching** — "this corresponds
to standard math `X`" in place of describing the thing in 213-native operational primitives. It is
listed in the failure-mode catalog with its correction: *describe in 213-native operational
primitives.* The whole of this book is that correction carried out for the orbit/axis/disc
structure.

## 1.3 A sharper hazard: `∅`-axiom-correct is not 213-native

The subtle point — the one that makes this more than a vocabulary complaint — is that **a theorem
can be machine-checked, `∅`-axiom, and PURE, and still be imported mathematics.** Purity certifies
that no foreign *axiom* was used. It says nothing about whether the *objects* are native.

`ℤ[i]` is a bare structure of two integers with the Gaussian product law; nothing in its
definition mentions the atomic counts `NS, NT, d`. A theorem about its units is true and pure —
and it is Dirichlet's unit theorem, not a fact about the residue. The file that proves it says so
in its own docstring: *the classical Dirichlet trichotomy made `∅`-axiom.* Purity and nativeness
are orthogonal, and conflating them is how imported mathematics enters a framework that formally
forbids it.

## 1.4 The two questions

So the book asks two questions of the orbit/axis/disc structure, and answers both.

1. **What is it, in 213's own primitives?** (Chapters 2–5.) Answer: a readout of one residue
   through a fixed tower of Lens choices — count, iterated count, difference — terminating in a
   single fact about non-square counting.

2. **Is it foundational?** (Chapter 5–6.) Answer: no. The Cassini and everything above it sit at
   least three Lens-steps above the residue. The foundation is the slash itself, where there is
   no integer, no multiplication, and no determinant — only distinguishing.

The method throughout is the framework's own: when a structure looks like imported mathematics,
do not map onto it — descend, naming each rung in native primitives, until either the structure
dissolves into something native or the import is exhibited cleanly as decoration. By the end both
happen: most of the edifice is decoration, and the residuum is `2` is not a square.
