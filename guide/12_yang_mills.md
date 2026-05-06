# 12 — Yang–Mills & Gauge

**Tier:** T1/T3 hybrid (T1 for mass gap statement; T3 for full proof)
**Status:** Mass gap *statement* formalized in Lean; full proof open.
**Lean:** `Physics/YangMillsGap.lean`, `Physics/Couplings/PhotonKernel.lean`,
`Physics/Couplings/AsymptoticFreedom.lean`.

## Best current statement

213 reformulates Yang–Mills as a discrete lattice problem at d = 5
with cycle space of K_{3,2} as the bipartite gauge graph. The mass
gap is then a **finite-dimensional** statement, not a continuum one.

### Mass gap (paper8 formulation)

`paper8_yang_mills_lean.tex` states the mass gap as a Lean theorem
(machine-verified):

```
∀ G ∈ {SU(3), SU(2)}, ∃ Δ > 0 :
  inf{spec(H_G) − vacuum} ≥ Δ
```

with Δ given by the rational expression in (NS, NT, d). For SU(3):

```
Δ_SU3 = α_GUT · m_p · (rational atomic factor)
```

Lean status: the *statement* is closed (paper8 cites
`native_decide`-verified inequalities). The *full Clay-Millennium
proof* — that the lattice formulation matches continuum YM in the
appropriate limit — is **open**.

### Confinement / no-go theorems

- 1/α₃ = 8 (Ch. 10) — color confinement formula closed.
- `paper8` no-go: continuum massless gauge field over d = 5 lattice
  cannot satisfy R4 (`Meta/R4Codomain.lean`) — formal incompatibility.

### Hadamard, deficit angle

Auxiliary lemmas in `paper8` (`thm:hadamard`, `thm:deficit`) are
machine-verified; they connect the gauge story to the cohomological
calculus of Ch. 14.

## 213 sharpening

- "Why the mass gap exists" → answer: forced by R1–R4 typeclass
  constraints on the gauge codomain; massless solutions violate R4.
- "Why color confinement" → answer: 1/α₃ = NS² − 1 = 8 at d = 5
  (Ch. 10 cross-reference).
- The Clay-Millennium problem is recast: instead of "prove existence
  of YM theory + show mass gap", 213 says "prove the lattice
  formulation is the correct discretization, and the mass gap follows
  by `decide`".

## Open / next

- **Continuum-limit equivalence proof** (the actual Clay problem).
  213 has the gap; whether 213's lattice ↔ continuum YM is open.
- Tighten Δ value to ppm (currently rational expression, not yet
  numerically extracted).
- Yang-Mills on SU(N) for general N — currently only SU(3), SU(2).

## Sources

- `papers/paper8_yang_mills_lean.tex`
- `papers/drlt-book/chapters/ch15_yang_mills.tex`
- `lean/E213/Lib/Physics/YangMillsGap.lean`,
  `PhotonKernel.lean`, `AsymptoticFreedom.lean`.
- `lean/E213/Meta/R4Codomain.lean` (R4 no-go for massless gauge).
