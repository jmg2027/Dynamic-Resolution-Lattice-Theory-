# G61: 213-tower research candidates (다 후보로 보존)

## Status

**Exploratory research note.**  Documents all candidates raised
during 2026-05-09 session re: "what is the 213-tower (≠ CD-tower)",
to be investigated.  Not formalized yet.

## Origin

User correction (2026-05-09): "난 cd타워를 원한게 아니라 213타워의
일반화와 올라갔을때의 동정 및 상태를 원했던 것인디… 글구 L0->L1도
Z말고 뭐가 있을수도 잇자노… 글구 이 조사는 P(x)를 바탕으로 수행해야
하는 것 아니려나"

CD-tower (well-known Hurwitz tower starting from ℝ) is NOT the same
as the 213-tower.  The 213-tower should be:
- 213-internal (no external Hurwitz frame imported)
- driven by **Möbius P(x) = (2x+1)/(x+1)**, matrix `[[2,1],[1,1]]`
- starting from a 213-native L0 (not necessarily ℕ)
- with growth rate **φ²** (not 2)

## Candidate spectrum

### A. L0 candidates (what is the seed?)

| L0 candidate | 213 reading | comment |
|---|---|---|
| ℕ | counting (most familiar) | requires "Nat" external |
| Raw | pointing-residue itself (G29) | most 213-native |
| {★} | singleton | minimum data |
| ∅ | absence | residue-as-pure-absence |
| Bool = {0, 1} | binary atom | NS=2 axis |
| Fin 5 | the universe | d=5 = NS+NT |
| {atom, anti-atom} | Raw atomic level | binary axis at L0 |

**Most 213-native**: Raw (self-referential via slash, P-style).

### B. L0 → L1 transition candidates

If L0 = ℕ, possible L1's:

| L0 → L1 | extension type | result |
|---|---|---|
| ℕ → (ℕ,ℕ)/~₊ | Grothendieck additive completion | ℤ |
| ℕ → (ℕ,ℕ)/~× | multiplicative completion | ℚ₊ |
| ℕ → ℕ ⊕ {⊥} | annihilator | ℕ + bottom |
| ℕ → 2-coloring of ℕ | sign-bit | signed (no add structure) |
| ℕ → ℕ × ℕ (no quotient) | free product | ℕ² lattice |
| ℕ → ℕ[ε]/(ε²) | dual numbers | ε-augmented ℕ |
| ℕ → ℤ[ω]/(ω³=1) (direct) | 3-fold cyclic | "3-side" Eisenstein-like |

**Most familiar**: Grothendieck → ℤ (= "2-side extension")

### C. L1 → L2 fan-out (Dirichlet 4-way)

Once at ℤ, the next CD-style step has 4 distinct base extensions
(per Dirichlet unit theorem, formalized in G53):

| L1 → L2 | extension | unit count | "k-side"? |
|---|---|---|---|
| ℤ → ZI = ℤ[i] | i² = -1 | 4 | 4-side |
| ℤ → ZSqrt[-D] (D≥2) | √-D added | 2 | 2-side |
| ℤ → ZOmega = ℤ[ω] | ω³ = 1 | 6 | 6-side (3·2) |
| ℤ → Hurwitz | (1+i+j+k)/2 | 24 | 24-side (binary tetrahedral) |

### D. P(x) fixed-point reading

P(x) = (2x+1)/(x+1) iteration:
- P(0) = 1, P(1) = 3/2, P(3/2) = 8/5, ... → φ
- Fixed points: φ ≈ 1.618 (attractor), -1/φ ≈ -0.618 (repeller)
- Eigenvalues of [[2,1],[1,1]]: φ² ≈ 2.618, 1/φ² ≈ 0.382

**213-tower meta fixed point candidate**: φ (= positive P-attractor)

### E. "213-number" candidates

| Definition | what it is |
|---|---|
| ℤ[φ] = ℤ[(1+√5)/2] | ring of integers in ℚ(√5) |
| P-orbit of seed 0 | {F_{2n}/F_{2n+1}} → 1/φ |
| Fibonacci pair (F_n, F_{n-1}) | vector form |
| Pell-Fib closure | algebraic closure of P |
| Z[√5]-lattice | Eisenstein-like for √5 |

**Most natural**: ℤ[φ] — already algebraic, lattice-discrete,
matches the Möbius P signature.

### F. Growth rate comparison

| Tower | growth per step | source |
|---|---|---|
| CD-tower | factor 2 (dimension doubling) | Cayley-Dickson |
| 213-tower (P-driven) | factor φ² ≈ 2.618 | Möbius P eigenvalue |
| Fibonacci (single) | factor φ ≈ 1.618 | one Fib step |
| Pell | factor (1+√2) ≈ 2.414 | Pell recurrence |

If the 213-tower is P-driven, its growth rate is **φ²**, distinct
from both CD-tower (2) and pure Fibonacci (φ).

### G. Structural questions to investigate

1. Does the L0→L1→L2→… P-iteration give a unique trajectory, or
   does it fan out at every step (like CD does at L2)?
2. Is there a 213-internal L0 that makes the tower "self-grounding"
   (no external ℕ needed)?
3. Does the **Raw/Signed.lean** swap-as-negation already give the
   L0→L1 step in 213-native terms?
4. What's the "3-side extension" (analog of 2-side ℕ→ℤ)?
5. Does the tower stabilize at some L_∞, or is it strictly
   ascending without limit point in 213's resolution?

## Direction taken

User selected (2026-05-09): "ℕ→ℤ→ℤ[i] direction first.  Is ℕ→ℤ a
2-side extension?  Then what's a 3-side extension?"

→ Pursued in `G62_two_side_three_side_extension.md`.

## See also

- `lean/E213/Theory/Raw/Mobius.lean` — P matrix
- `lean/E213/Theory/Raw/Signed.lean` — swap-as-neg (ℕ→ℤ structurally)
- `lean/E213/Theory/Internal/Int213.lean` — ℤ in 213-native form
- `research-notes/G29_residue.md` — pointing-residue, P fixed-point
- `research-notes/G57_213_mobius_signature.md` — Möbius signature
- `research-notes/G58_algebra_tower_completion.md` — CD-tower closure
- `research-notes/G60_tower_ascent_fixed_point.md` — CD-tower fixed point
