# The slash-reading atlas (geometric)

*Tier 1 (research-notes), volatile.  One residue — the slash, "object = the
relation of two objects" (`02_axiom.md` §2.2) — read through different Lenses
gives different geometric objects, and different structural invariants surface.
This is the geometric face of `06_lens_readings.md` §6 "Lens readings of the same
residue".  Started from Mingu Jeong's "object IS two distinct objects" sketch.*

## The generating space (the dials)

The construction "every relation of two objects is itself an object, recurse"
has a choice at each step.  The atlas is the product of these dials; each
setting is a reading of the slash:

1. **Directedness** — undirected (`a/b = b/a`, the axiom symmetry §3.3) vs
   directed (the difference-Lens sign, §6.7).
2. **Quotient amount** — how much of prim-distinctness is honored: full quotient
   (new object identified with a combination of its parents) → collapse; free
   (new object = independent direction) → dimension growth; algebraic (new
   object distinct but `P`-related) → Stern-Brocot.
3. **Combining map** — the geometric/algebraic form of "relation": arithmetic
   mean `(a+b)/2`; mediant `(p+r)/(q+s)`; orthogonal adjunction; off-segment
   complex map `x+(y−x)w`; geometric mean; other Möbius/`SL(2,ℤ)` maps.
4. **Growth rule** — which pairs spawn: adjacent only (dyadic / Stern-Brocot)
   vs all pairs (complete) vs directed pairs.
5. **Readout invariant** — what you measure of the resulting object: positions,
   depth / ruler, angles, volume, the generating matrix's trace/det/disc,
   spectrum, dimension.

## Explored cells (this session)

| script | reading of the slash | geometric object | limit | invariants surfaced | 213 link |
|---|---|---|---|---|---|
| `object_as_relation.py` | undirected betweenness (midpoint); also the directed off-segment variant | dyadic lattice on a segment / de Rham (Lévy) fractal | segment `[a,b]` (dim 1) / fractal curve | — (midpoint washes them out); sign for the directed map | quotient collapse `0≡∞≡point` (§6.5); difference-Lens (§6.7) |
| `intermediate_shape.py` | resolution-depth of betweenness | self-similar tent hierarchy | Takagi / blancmange | 2-adic valuation (ruler sequence), self-similarity | the dynamic-resolution lattice — structure lives at finite resolution |
| `dimension_growth.py` | free / orthogonal (no quotient) | regular `n`-simplex | `Δ^∞` (infinite-dim) | dimension = count (prim-distinct ⟺ independent) | the **dimension-Lens** (`dimension_lens.md`) |
| `simplex_intermediate.py` | shape of the regular `n`-simplex vs `n` | regular `n`-simplex | orthonormal corners + measure-zero body | `arccos(±1/n)→90°`, `r/R = 1/n`, `V→0` | no-exterior = the partition-of-unity / sum constraint; concentration of measure |
| `mediant_constants.py` | **algebraic** (mediant / Möbius `P`) | Stern–Brocot tree | every rational once (dim 1, structured) | `P=[[2,1],[1,1]]`, `trace 3 = N_S`, `det 1 = glue`, `disc 5 = N_S+N_T`, `φ²,1/φ²` | §3.5 Möbius form; `K_{3,2}^{(c=2)} = (3,2,5,2)`; `SternBrocotMarkov` |
| `constant_threshold.py` | the knob `a` from collapse to `P` (`M_a=[[a,1],[1,1]]`) | Möbius spine | `x*(a)` (quadratic irrational) | `det=a−1`; blind at `a=1` (det 0); `3,5,φ` at `a=2` | **C1 test**: blind ⟺ `det=0`; constants ⟺ forced `a=2` (§3.2 = §3.5) |
| `derham_family.py` | directed off-segment, swept (`x+(y−x)w`) | de Rham curves (Lévy, Cesàro–Koch, …) | self-similar fractals | similarity dim (Moran `\|w\|^d+\|1−w\|^d=1`) | **K4 breadth**: many shapes from one `w`; dimensions = the non-∅-axiom edge |

## Further readings (exploratory catalog)

More combining maps, each a Lens with its own limit + intermediate stage
(`more_lens_readings.py`).  Tier-1 exploratory — a reading promotes only when a
discrete cell closes ∅-axiom.

| slash read as | combining map | limit | intermediate shape | 213 link |
|---|---|---|---|---|
| **power-mean between** | `M_p(x,y)=((x^p+y^p)/2)^{1/p}` | warped segment | skewed dyadic lattice | the "between" is a *family*; arithmetic (`p=1`) is the symmetric member, geometric/harmonic the skewed ones |
| **XOR / Nim** | `x ⊕ y` (bitwise) | Sierpinski gasket (dim `log3/log2≈1.585`) | `n`-bit table (Pascal mod 2) | the binary / carryless reading; discrete self-similar |
| **mediant (Ford)** | `(p+r)/(q+s)` | Ford circle packing (all ℚ) | denominator `≤ Q` | the mediant's circle-packing face; tangency ⟺ mediant neighbours (§3.5 `P`) |
| **modular** | `(x+y) mod n` | the `n`-gon `ℤ_n` → circle | partial `n`-cycle | a **finite / periodic** limit (not continuum/fractal); ties to mod-`p` periods (`Px/ModPPeriods`) |
| **golden rotation** | rotate by the golden angle | equidistribution (sunflower) | first `N` points | `φ` = the most uniform rotation — `φ` returns from §3.5 as the equidistribution optimum |
| **concatenation** | word `x·y` | Cantor set (dim `log2/log3≈0.631`) | `2^n` intervals | the syntactic reading (§6.4 internalisation); the slash read as word-formation |

Two structural observations: (i) the limit is not always a continuum or a
fractal — the modular reading's limit is **finite/periodic**, a third kind; (ii)
`φ` reappears here as the *equidistribution* optimum (golden rotation), the same
`φ` that §3.5 reads as the residue's algebraic measure — one number, two frames.

### Batch 2 (`more_lens_readings_2.py`)

| slash read as | combining map | limit | intermediate shape | 213 link |
|---|---|---|---|---|
| **mediant ↔ midpoint glued** | Minkowski `?(x)` | the singular `?` function | continued-fraction truncation | sends the Stern–Brocot order to the dyadic order — the *mediant* reading and the *betweenness* reading fused into one map |
| **pairing** | Hilbert curve | space-filling (dim 2) | order-`n` curve | the slash read as a coordinate pairing |
| **Pascal mod `p`** | `C(i,j) mod p` | mod-`p` Sierpinski (dim `log(p(p+1)/2)/log p`) | `p^k`-row table | the XOR reading (`p=2`) is one member of a prime-indexed family |
| **golden substitution** | `1→10, 0→1` (cut-and-project) | Fibonacci word / quasicrystal | `n`-th iterate | `φ` as **aperiodic order** — a third `φ`-frame |
| **mediant on ℍ** | mediant acting on the hyperbolic plane | Farey / modular tessellation | depth-`n` ideal triangles | the mediant (§3.5 `P`, `SL(2,ℤ)`) read as hyperbolic geometry |
| **complex squaring** | `z ↦ z²+c` | Julia set | escape-time iterate | the relation read as a complex map |

Cross-frame: `φ` now stands in **three** frames — the residue's algebraic
measure (§3.5, eigenvalue of `P`), the most uniform rotation (golden
equidistribution, batch 1 E), and aperiodic order (the Fibonacci/quasicrystal
reading, batch 2 D).  And Minkowski `?(x)` is the session's own thesis as a
single function: it conjugates the *mediant* reading (which surfaces the
constants) to the *betweenness* reading (which does not), so the singular,
nowhere-smooth gap between them *is* the gap between the two atlas cells.

## The meta-thesis (the research spine)

**Which readings surface the structural constants `(3,2,5,P,φ)` and which are
blind to them?**  Observed pattern: the maximally-symmetric / metric combining
maps (arithmetic mean, regular simplex) *quotient away* the asymmetry the
constants live in and surface nothing; the **algebraic** combining map — the
slash's own form, the mediant generated by the Möbius `P` — surfaces them
directly.

**Tested** by the one-knob family `M_a=[[a,1],[1,1]]`, `det=a−1`
(`constant_threshold.py`): blind ⟺ `det=0` ⟺ `a=1` (the averaging/midpoint
rank-1 collapse — why the first four renderings were blind); the specific
`3,5,φ` sit at `a=2`, which is simultaneously the forced count-Lens minimum
("two + binary", §3.2) and the unimodular glue (`det=1`, §3.5).  The constants
are not tuned — "two somethings" *is* the golden point.  The loop closes back
onto §3.2 / §3.5.

## Roadmap — unexplored readings (the "lots more shapes")

- ~~**Sweep the de Rham parameter `w`**~~ — explored (`derham_family.py`): the
  fractal family (Lévy, Cesàro–Koch, …) as one continuous dial.  Still open: the
  fractal *dimensions* (Moran / Hausdorff) have no ∅-axiom shadow.
- ~~**Other Möbius / `SL(2,ℤ)` generators** beyond `P`~~ — **CLOSED** ∅-axiom:
  the metallic generator tower `N_k=[[k,1],[1,0]]` (`det=−1 ∀k`, golden the
  `disc=d=5` minimal rung, `N_1²=P`) in `Px/MetallicGeneratorTower.lean`.
- **The midpoint ↔ mediant interpolation**: denominator `2` ↔ `q+s`.
  Continuously switch the Möbius structure on and off; locate the threshold
  where the constants appear (tests the meta-thesis directly).
- **Directed mediant** (signed Stern–Brocot): the difference-Lens ℤ-completion
  on the tree.
- ~~**`K_{3,2}^{(c=2)}` directly**: split the distinguishing into state (3) /
  transition (2) per §6.2 and embed bipartitely~~ — **CLOSED** ∅-axiom:
  `BipartiteDecomp/K32Adjacency.lean` (the bipartite adjacency / degree structure
  the regular simplex erased; 17 PURE).  Still open: connect to the full closure
  form `R(N_S,N_T,d,c)·Π(1+κᵢαᵢ^{nᵢ})`.
- **Higher `Rawⁿ` readings** (flat ontology §6.3): the relation of `n`-tuples,
  not just pairs → higher simplicial / hypergraph shapes.
- **Spectral readouts**: adjacency / Laplacian spectrum of the growth graph —
  which spectra carry `3,2,5`?
- **`p`-adic readings**: connect to the existing `p`-adic frontier
  (`frontiers/G123`–`G125`).

## Promotion path

- The **mediant / Möbius / constants cell is closed** ∅-axiom in Lean
  (repo-first finding; build + `scan_axioms` verified PURE): the `Mobius213/Px`
  sub-tree (30 files), promoted to
  `theory/math/algebra/mobius213_p_orbit_closure.md`.  The **C1 threshold** (this
  session) is now a theorem there: `Px/MetallicThreshold.lean` — det = a−1,
  collapse (det 0) at `a=1`, golden (det 1, trace 3, disc 5) at the forced
  `a=2`, metallic tower beyond (`metallic_threshold_master`).  Key cites — det glue
  `Mobius213OneAsGlue.{one_is_det, mobius_det_eq_ns_minus_nt, mobius_det_is_unit}`,
  `Px.CassiniUniversal.cassini_universal` (det=1 ∀n); the `det=0` collapse end
  `Mobius213K33Bridge.k33_NS_minus_NT_eq_zero`; the `(2,3,5)` lock
  `Px.FibonacciAtomicLock.fibonacci_atomic_lock_master`.  The geometric C1
  exploration *re-derived* this; its only addition is the one-dial narrative.
- **Now also closed** ∅-axiom (build + `scan_axioms` PURE, 11/0): the
  dimension-Lens half — `prim-distinct ⟺ linear independence` + approach to
  orthogonality — in `AngleStructure/SimplexOrthogonality.lean` (rational-Gram,
  `cos = −1/n` cleared to `Nat`, no trig).  Key cites: `cos_mag_is_inv_n`,
  `partition_dependence`, `uncentered_orthonormal`, `cos_dim_strict_mono`,
  `simplex_orthogonality_master`.  See `dimension_lens.md`.
- The atlas stays tier-1; closed cells already live in `theory/`.  Frontier
  registered in `research-notes/frontiers/G205`.

## Caution (self-check #0)

Shapes, dimensions, constants are **Lens outputs**, not Raw commitments
(`02_axiom.md` §2.5).  The atlas catalogs *readings*; the residue is outside
every cell's image (`FlatOntologyClosure.object1_not_surjective`).  No reading
is "what the residue IS."
