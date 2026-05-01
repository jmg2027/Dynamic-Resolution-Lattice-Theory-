# Phase 2 — Redrawing the Universe with 213 Alone

Phase 1 (E213/Physics/, 68 files) derived *known precision quantities*
from atomic primitives.

Phase 2 asks again by **forgetting everything and starting over**:

> *What can we say about the universe using only 213 axioms?*

---

## Progression (educational + intuition order)

### 1. `Origin.lean` — *How many dimensions?*

213 axiom + Atomicity → **d = 5**, any other choice violates the axiom.
This single theorem is the *seed* of Phase 2.

```lean
theorem only_one_cosmos_dim :
    ∀ n, Atomic n ↔ n = 5 := ...
```

---

### 2. `Shape.lean` — *So what does it look like?*

```
  ●───●───●         ← 3-block (a-block)
   \  |  /          
    \ | /           
     \|/            
      X             ← cross-pairs (6)
     /|\            
    / | \           
   /  |  \          
  ●───●             ← 2-block (b-block)
```

5 points = 3 points + 2 points.  Edges: 3 (triangle) + 1 (line) +
6 (cross) = 10.

In mathematical terms: **4-simplex Δ⁴ with (3,2) vertex partition**.

---

### 3. `Existence.lean` — *What are the 5?*

  `Vertex := Fin 5`.
  
  Whether two vertices are *the same* is `DecidableEq` (axiom decision).
  
  Block classification:
  - `inBigBlock v` — belongs to the 3-block
  - `inSmallBlock v` — belongs to the 2-block

213's *maximum ontology*: "5 vertices, (3,2) size partition". No
further names or meanings until a Lens is added.

---

### 4. `Pairs.lean` — *What is between pairs?*

10 pairs automatically fall into three categories:

| Category | Count | Meaning |
|---|---|---|
| AA | 3 | Both in big block (triangle interior edge) |
| BB | 1 | Both in small block (the line itself) |
| AB | **6** | cross — **K_{3,2} bipartite edges** |

**6 cross pairs = K_{3,2} bipartite graph. Naturally emerging.**

(Phase 1's PhotonKernel discovered cycle space b_1 = 8 = α_3 on top
of this — now confirming that *the underlying K_{3,2} itself* is
axiom-derived.)

---

## Everything 213 *Can Say* (end of Phase 2)

```
Universe:
  d = 5 (dimensions)
  5 vertices (what the 5 are)
  (3, 2) partition (block sizes, labels are Lens)
  10 pair information (3 AA + 1 BB + 6 AB)
```

This is *all*.

To go further:
- *labels* (which is spatial, which is temporal) → **add Lens**
- *measurements* (mass, coupling, ...) → **Lens output**
- *force* (gauge) → **Lens classification (channel)**
- all remaining physics → **Lens output**

---

## Phase 1 vs Phase 2 Comparison

| | Phase 1 | Phase 2 |
|---|---|---|
| Starting point | Known precision quantities | 213 axioms only |
| First import | NS=3, NT=2 *numerically* | Atomicity *theorem* |
| Answer | 137, m_p, etc. | d=5, 5 vertices, 10 pairs |
| Atomic atoms | appear | are defined |
| Use | verify existing physics match | state semantic starting point |

The two tracks *complement each other*. Phase 1 is the endpoint
(precision match), Phase 2 is the starting point (axiom meaning).

---

### 5. `Time.lean` — NT sector = dyadic resolution

NT = 2 is the atomic small block size.  Utilizing the *math track
bridge*: NT steps are unfolded as *binary dyadic division*.

  `NT_n_steps_yield_two_pow : bisectN^n start = 2^n branches`

(Math track `Real213/Phase A→C` dyadic geometry = the axiom-level
meaning of the physical NT sector.)

---

### 6. `Space.lean` — NS sector = ternary resolution

NS = 3 is the atomic big block size.  3^n ternary unfolding.

The NT vs NS *asymmetry* (3/2)^n is the axiom-level origin of Phase 1's
m_μ/m_e factor, Y-norm, and Fibonacci F_5/F_4.

---

### 7. `Observable.lean` — measurable quantities

*9 integers* definable with 213 axioms alone:
d, NS, NT, c, total_pairs, AA, BB, AB,
num_directed_edges, cycle_space_dim.

Phase 1's precision quantities are Lens outputs of these 9.

---

### 8. `Force.lean` — 3 channels = 3 forces?

  - AA (3 pairs): NS-internal, color-like / α_3
  - BB (1 pair):  NT-internal, weak-like / α_2
  - AB (6 pairs): cross-sector, EM-like / α_1

★ 3 forces emerge naturally ★ (channel size ≠ direct proportion to
coupling strength; Phase 1 prefactors have a deeper origin.)

---

### 9. `Edges.lean` — c=2 doubling, b_1=8

c = 2 = NT atomic size.  6 undirected → 12 directed.
Cycle space b_1 = 12 - 5 + 1 = 8 = NS² - 1.

**8 = 1/α_3** (axiom-level arithmetic underlying Phase 1 PhotonKernel).

---

### 10. `Lens.lean` — Hypervisor explicit Lens

Direct use of the math track `Hypervisor/Lens.lean` pattern. First
explicit Lens objects (parityLens, bCountLens) — operating on Raw at
the *Hypervisor-layer*, not App-layer arithmetic.

---

### 11. `Capstone.lean` — single synthesis of 10 files

26-conjunct theorem, ≤ propext + Quot.sound.  Formal synthesis of
*all* of Phase 2.

---

## Build

```bash
cd 213/framework
lake build E213.Physics.Phase2.Capstone   # full synthesis (10 files)
```

All 0 sorry, ≤ propext + Quot.sound (Lean 4 core only).
Most files are *completely axiom-free*.

---

## Operating Principles

CLAUDE.md: no words "observer/structure/relation/space/cognition" in
axiom descriptions. Only "primitive distinction". Everything else is
stated as Lens output.

`AUDIT.md` — cross-audit with math track (extreme rigor):
**Phase 2 has no violations**. Follows App/Simplex pattern exactly.
