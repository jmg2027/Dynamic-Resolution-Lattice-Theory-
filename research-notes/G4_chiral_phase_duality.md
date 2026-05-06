# G4 — Chiral / Phase Duality of d = 5

**Date:** 2026-05-XX (continuing G2/G3)
**Author:** Mingu Jeong (insight)
**Formalisation:** Claude (Anthropic)
**Status:** Foundational principle.  Formal anchor:
`Math/Trajectory/PhaseChiralBridge.lean`.

---

## 0. Thesis (one sentence)

The atomic shape `(NS, NT, d) = (3, 2, 5)` supports two
*algebraically-distinct* decompositions of the same K_{3,2}^{(2)}
skeleton — *chiral* (vertex-count, $5 = 3 + 2$) and *phase* (walk-
period, $6 = 2 \times 3$ via CRT) — and 213 uses both at once.

---

## 1. The user's algebraic intuition

> "(a + b·ω₂) + (c + d·ω₃) = e + f·ω₅ ?  Where ω_n is the n-th
> root of unity (ω₂ = -1, ω₃ a 3rd root, ω₅ a 5th root)."

Read literally as cyclotomic algebra, this is *not* a standard
identity: $\mathbb{Q}(\omega_3) \not\subseteq \mathbb{Q}(\omega_5)$
($3 \nmid 5$), and $[\mathbb{Q}(\omega_5) : \mathbb{Q}] = 4$.  Cyclotomic
fields don't combine that way.

But read as a 213-internal *structural* statement, it is *exactly*
the chiral decomposition of the atomic shape — and it's correct in
that frame.  Below is the two-view bridge.

---

## 2. The two views

### View A — phase walk (cyclotomic)

K_{3,2}^{(2)} with constant input has period 6 = LCM(2, 3).  Walking
gives a $\mathbb{Z}/6$ trajectory, which by CRT decomposes as
$\mathbb{Z}/6 \cong \mathbb{Z}/2 \times \mathbb{Z}/3$:

  - $\mathbb{Z}/2$ component = `parity` (S/T side after $n$ steps)
  - $\mathbb{Z}/3$ component = `mod3` (S-vertex index, modulo 3)
  - Together: `mod6 n ↔ (parity n, mod3 n)`

In cyclotomic terms this is the **Eisenstein 6th-roots-of-unity
walk** (ring $\mathbb{Z}[\omega_6] = \mathbb{Z}[\omega_3]$).

Already formalised in `Kernel/Tactic/Mod213.lean`:
  - `Mod213.mod6_parity : parity (mod6 n) = parity n`
  - `Mod213.mod6_mod3   : mod3   (mod6 n) = mod3 n`
### View B — chiral split (vertex-count)

The 5-vertex skeleton of K_{3,2}^{(2)} decomposes as the disjoint
union of NS spatial vertices (S-side) and NT temporal vertices
(T-side):

$$
\text{Fin 5} = \underbrace{\text{Fin 3}}_{\text{S-side, NS}}
              \sqcup \underbrace{\text{Fin 2}}_{\text{T-side, NT}},
\qquad NS + NT = d
$$

Lifted to Hilbert space (`Math/Linalg213/Chiral.lean`):

$$
\mathbb{C}^5 = \mathbb{C}^3 \oplus \mathbb{C}^2
            = \text{VecS} \oplus \text{VecT}
$$

This is **direct-sum** decomposition (counting), *not* cyclotomic.

---

## 3. Why d = 5 supports both — atomicity at work

The two views coexist *because* atomicity forces $(NS, NT, d) =
(3, 2, 5)$.  Specifically:

  - **View A needs $\gcd(NS, NT) = 1$** so CRT decomposes
    $\mathbb{Z}/(NS \cdot NT) \cong \mathbb{Z}/NS \times \mathbb{Z}/NT$.
    Here $\gcd(3, 2) = 1$ ✓.
  - **View B needs $NS + NT = d$** as a structural identity.
    Here $3 + 2 = 5 = d$ ✓.

Both views agree on the same K_{3,2}^{(2)} graph.  This co-existence
is *forced* by `Firmware/Atomicity/*` — not coincidence.

The user's "$(a + b\omega_2) + (c + d\omega_3) = e + f\omega_5$" reads
as a bigraded-decomposition identity in 213-internal:

| Symbol | View | Meaning |
|---|---|---|
| $a + b\omega_2$ | A (phase) | $\mathbb{Z}/2$ trajectory state |
| $c + d\omega_3$ | A (phase) | $\mathbb{Z}/3$ trajectory state |
| $\oplus$ (chiral) | B | direct sum across NS / NT split |
| $e + f\omega_5$ | A∩B | element of Vec 5 = ℂ³ ⊕ ℂ² |

The "+" between the two is *not* cyclotomic addition but
**chiral direct sum** — pairing the S-side phase (mod 3) with the
T-side phase (mod 2) in the bipartite skeleton.

---

## 4. Forward consequences

Every "$d = 5$" theorem in 213 implicitly uses one or both views:

  - `Physics/Simplex/Counts.{NS, NT, d}` — atomic constants
  - `Math/Linalg213/Chiral.lean` — chiral split (View B)
  - `Math/Cohomology/Dyadic/Signature.lean` — K_{3,2}^{(2)} walk
    (View A: phase trajectory)
  - `Math/Cohomology/Dyadic/SignatureBipartite.lean` — bipartite
    alternation theorem (View A connecting parity to S/T side,
    pending migration via `Mod213.parity` instead of `% 2`)
  - `Math/Cohomology/Dyadic/AtomicityConnection.lean` — bridges
    K_{3,2}^{(2)} to atomic counts (early form of this duality)

All 0-axiom α_em / mass / cosmology results pull from one or both
views.  Any future "5"-related theorem will too.

---

## 5. Formal anchor

**`Math/Trajectory/PhaseChiralBridge.lean`** records both
views as ∅-axiom theorems and ties them together as a single
`atomic_five_dual` capstone:

```lean
theorem chiral_count : NS + NT = d                      -- View B
theorem phase_crt (n : Nat) :
    parity (mod6 n) = parity n
  ∧ mod3 (mod6 n) = mod3 n                              -- View A
theorem atomic_five_dual : … combines the two           -- bridge
```

Any future "5"-related work imports this file and uses one or both
theorems as the canonical bridge.

---

## Cross-references

  - `seed/AXIOM/00_nature.md` §1.3 — atomicity (NS, NT, d) = (3, 2, 5)
  - `Firmware/Atomicity/*` — atomicity forcing
  - `Kernel/Tactic/Mod213.lean` — phase-walk primitives (View A)
  - `Math/Linalg213/Chiral.lean` — chiral split (View B)
  - `Math/Trajectory/PhaseChiralBridge.lean` — formal bridge
  - `research-notes/G2_trajectory_principle.md` — trajectory frame
  - `research-notes/G3_raw_as_universal_trajectory.md` — Raw as
    universal trajectory space (this duality is one Lens choice)
