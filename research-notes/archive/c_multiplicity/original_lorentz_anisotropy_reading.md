# The original `c = 2` Lorentz-anisotropy reading (pre-seed, recovered)

**Provenance.**  Recovered from pre-seed history (commit `b91703301`,
2026-04-10, *"Part 14: 심플렉스 해석 — 격자점 = 4-심플렉스"*), file
`axiom/from_one_axiom.md` §12.4 + §14.8.  This predates the squashed seed
(`5855695`, 2026-06-03) and was lost from the working tree in the
reorganisations after it.  Preserved here verbatim because it is the
**originating reading** of `c = 2` — the "time edge is twice as short as the
space edge" anisotropy the later edge-multiplicity formalism grew out of.

This is an *archive record of a path*, not a current-tier claim.  For the
canonical status of `c` see `theory/physics/foundations/atomic_constants.md`
and the frontier `research-notes/frontiers/atomic_c_multiplicity_forcing.md`;
for the bridge to the current edge-multiplicity / layer-count form see
`theory/essays/cohomology/c_counter_as_layer_count.md` (the "Physical
(anisotropy / temporal-refinement)" reading).

## Verbatim original — §12.4 "c = 2 의 유도"

```
시간 edge: 연속 진화 ψ(t) → ψ(t+dt)
  W_T = |⟨ψ(t)|ψ(t+dt)⟩|²/d → 1/d (dt→0)
  d_T = -ln(1/d) = ln d = ln 5

공간 edge: 독립 이웃
  W_S = |⟨ψ_i|ψ_j⟩|²/d → 1/d² (랜덤)
  d_S = -ln(1/d²) = 2 ln d = 2 ln 5

  c = d_S/d_T = 2 ln 5 / ln 5 = 2 (정확히)

기원: i (허수 단위)
  유니터리 진화 e^{-iHt} → 시간에만 위상 회전
  → W_T > W_S → d_T < d_S → c = 2
  → ds² = -4dt² + dx² + dy² + dz²

로렌츠 부호 (-,+,+,+) = 확률 보존 (|ψ|²=1) 의 귀결.
```

### Translation

```
Time edge: continuous evolution ψ(t) → ψ(t+dt)
  W_T = |⟨ψ(t)|ψ(t+dt)⟩|²/d → 1/d   (as dt→0)
  d_T = -ln(1/d) = ln d = ln 5

Space edge: independent neighbours
  W_S = |⟨ψ_i|ψ_j⟩|²/d → 1/d²        (random)
  d_S = -ln(1/d²) = 2 ln d = 2 ln 5

  c = d_S / d_T = 2 ln 5 / ln 5 = 2  (exactly)

Origin: i (the imaginary unit)
  unitary evolution e^{-iHt} → phase rotation in time only
  → W_T > W_S → d_T < d_S → c = 2
  → ds² = -4dt² + dx² + dy² + dz²

Lorentz signature (-,+,+,+) = a consequence of probability
conservation (|ψ|²=1).
```

## Verbatim original — §14.8 "심플렉스의 모양" (shape of the simplex)

```
c = 2 에서 (Part 12.4):
  d_T = ln5 ≈ 1.61 (시간 변)
  d_S = 2ln5 ≈ 3.22 (공간 변)

→ 정오포체(정규 5-cell)가 아닌 비등방 심플렉스:
  시간 방향으로 짧고, 공간 방향으로 긴 형태.
  이 비등방성 = 로렌츠 부호 (-,+,+,+).
```

(Translation: at c = 2 — temporal edge `d_T = ln5 ≈ 1.61`, spatial edge
`d_S = 2ln5 ≈ 3.22` — the 4-simplex is **not** a regular 5-cell but an
**anisotropic** one, *short in the time direction and long in the space
direction*; this anisotropy **is** the Lorentz signature `(-,+,+,+)`.)

## The mechanism (so the "twice" is not mistaken for a naive spacing)

The factor 2 is an **information-distance** ratio, `d := −ln(overlap)`:

  · a **temporal** edge connects `ψ(t)` to `ψ(t+dt)` — a *correlated*
    (unitary) pair, overlap `W_T → 1/d`, so `d_T = ln d`;
  · a **spatial** edge connects two *independent* neighbours, overlap
    `W_S → 1/d²` (the **square** — independence multiplies the two `1/d`
    factors), so `d_S = 2 ln d`.

Hence `c = d_S/d_T = (2 ln d)/(ln d) = 2`, *exactly*, for every `d` — the
`d = 5` is incidental to the ratio.  The "2" is the **square in `W_S = W_T²`**
read through `−ln`.  Its root cause is `i`: unitary evolution `e^{−iHt}`
puts phase rotation on the time axis only, which is what makes the temporal
overlap first-order (`1/d`) while the spatial one is second-order (`1/d²`).
The anisotropy `ds² = −4 dt² + dx²+dy²+dz²` (equivalently `d_S = 2 d_T`) is
the Lorentz signature, and it descends from `|ψ|² = 1`.

## Bridge to the current form (edge multiplicity / layer count)

In the current canonical form, the `K_{NS,NT}^{(c)}` `c` is an **edge
multiplicity** (parallel edge-layers per `(s,t)` incidence) and `c = 2`
there is a selected re-presentation of `NS²−1` (3 forced `(NS,NT,d)` +
the K32 `c` posited/removable).  **The anisotropy `c` of this note is NOT
that quantity** — the deep-research finding
`research-notes/frontiers/c_is_three_distinct_twos.md` shows they are
**distinct 2's** that share only the value:

  · the anisotropy `c = d_S/d_T = 2` is an **order/exponent** (the square
    `W_S = W_T²` through `−ln`), holds for **every `d`** (no
    graph-multiplicity content), and is the **Lorentz signature**
    `(−,+,+,+)`, sourced in `NT` / the period-2 sign / `i`;
  · the edge multiplicity is a **count** on the `c`-line `b_1 = 6c − 4`.

These cannot be identified: `V32Betti.mult_parity_orthogonal_to_cup_orientation`
proves the sign/`i` ℤ/2 (which carries the anisotropy) and the multiplicity
ℤ/2 act on **orthogonal data**.  So the earlier "one number, two Lenses"
bridge was **too generous** — it mislabels a signature/order quantity as a
reading of the multiplicity.  What *is* forced and physical in the original
passage is the **signature** (`(−,+,+,+)` from `|ψ|²=1` and `i`); the octet
`NS²−1` needs neither this anisotropy nor the edge multiplicity.
