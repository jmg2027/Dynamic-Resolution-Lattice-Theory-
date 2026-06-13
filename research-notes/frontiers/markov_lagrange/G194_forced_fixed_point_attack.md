# G194 — Direction (2): attacking `H` as a forced fixed point (Bool↔Nat), and where the forcing stops

The "real shot" at the kernel: attack Markov uniqueness `H` directly via the §4.3 / no-exterior
*forced-fixed-point* idea (`G193` B/C) — the realized `√(−1)` suborbit cannot be an external label, so it
must be forced by the residue-internal Vieta descent.  This note records the attempt, the precise point
where the forcing stops, the structural reason it stops there, and the ∅-axiom down-payment landed.

## A. The forcing is already maximal — the wall is exactly realizability

Walking the §20–§26 orbit tower against the forced-fixed-point idea shows the repo has *already pushed the
forcing to its limit*.  The "Bool symmetry-breaking" — reducing the `√(−1)` torsor to the residual
realizability freedom — is complete and ∅-axiom:

  - **window sections the `±1` (Bool) action**: `window_excludes_partner` — of `{u, c−u}` exactly the one
    `< c/2` is windowed; the order-2 element `−1` is broken by the window.
  - **free action** (`root_orbit_inj`, `root_orbit_inj_neg`): `e·u ≡ ±u ⟹ e ≡ ±1`; the unit-root group
    `SqrtUnity` acts freely on the roots — no two distinct unit-roots share an orbit point.
  - **distinct windowed roots ⟹ nontrivial multiplier** (`windowed_distinct_multiplier`): any two distinct
    windowed roots are related by `e ∉ {1, c−1}`.
  - **the full reduction** (`windowRealizedUnique_of_orbit`, `markov_max_unique_of_orbit`):
    `MarkovMaxUnique c` holds **iff** no nontrivial-unit-root image of a realized windowed root is itself
    realized — `H` = `OrbitRealizabilityH`.

So everything *forceable* — the count `2^(ω−1)`, the group, its free action, the window transversal — is
forced.  **The remaining content is purely realizability**: which of the `2^(ω−1)` genuine `√(−1)` roots
is the shadow of an actual Markov triple.  The forced-fixed-point attack reaches this wall and no further:
there is no additional *forced* reduction available without deciding realizability itself.

## B. Why the forcing stops here — the locality obstruction (the sharp 213-native statement)

The Bool↔Nat reading (`G193` B) makes the obstruction precise.  Restating the two self-reference forms on
the Markov objects:

  - **Bool object** = the `√(−1)` root mod `c` / the Cohn matrix `C² ≡ −I (mod c)` (order 4).  This lives
    at **fixed modulus `c`** (local).  All `2^(ω−1)` windowed roots are *equally valid* Bool objects —
    root-counting, being fixed-`c`, cannot separate them.
  - **Nat object** = the Vieta descent path, converging to the root `(1,2,5)`.  But the descent
    `c ↦ 3ab − c` **shrinks the modulus** at every step (the new max is smaller); the residue mod `c` is
    *not preserved* down the descent.

**The obstruction**: realizability — "this root is the shadow of a descending path" — is a **global**
property of the whole descent, while every *forced / fixed-`c`* structure (the count, the group, the free
action, the window) is **local** in `c`.  There is no `c`-local invariant that distinguishes the realized
root from the phantoms, because the distinguishing data is the *trajectory*, which leaves `c`.  This is
exactly why the local layer (root-counting) closes ∅-axiom while the global layer (realizability) is the
open conjecture — and exactly why the classical necessary-not-sufficient layer (Aigner orderings) is
*oriented / cross-`c`* (the continuant of the Christoffel word, `G191`): the orderings live at the global
level the forcing cannot reach locally.  **The forced-fixed-point attack cannot cross the wall because the
selector it seeks is non-local in `c`, and all forcing is local.**  (This sharpens, with a reason, the
boundary `G192` found via `DirectionFree`: same wall, now with the locality mechanism named.)

## C. Down-payment — a new ∅-axiom verified composite (`MarkovMaxUnique 985`)

Not a structural crossing, but a real new theorem and a concrete probe of the Bool↔Nat pattern:
`markov_max_unique_985_via_orbit` (`SternBrocotMarkov`, ∅-axiom).  `985 = 5·197` is the next `ω = 2`
composite Markov number (both primes `≡ 1 mod 4`, full `2^ω = 4` root explosion):

  - windowed roots `{183, 408}`;
  - **`408` realized** by the actual triple `(2, 169, 985)`: `(408·169) % 985 = 2`, and `408² + 1 = 985·169`;
  - **`183` phantom**: `183² + 1 = 985·34`, but no triple `(x, b, 985)` with `x ≡ 183b` exists (`decide`);
  - the `u₁ = u₂ = 408` case closes **structurally** (`root_orbit_inj` free action), not by `decide` —
    only the phantom check `∀ b, ¬ markovEq …` is decided.

This extends the structural-tower closure (previously the worked `ω = 2` case was `1325 = 5²·53`, realized
`507`, phantom `182`).

### Concrete Bool↔Nat data (two cases; no pattern claimed across them yet)

| `c` | factor | windowed roots | realized | its `u²+1 = c·?` | phantom | phantom `u²+1 = c·?` |
|---|---|---|---|---|---|---|
| `1325` | `5²·53` | `{182, 507}` | `507` (triple `(13,34,1325)`) | `1325·194` | `182` | — |
| `985` | `5·197` | `{183, 408}` | `408` (triple `(2,169,985)`) | `985·169` | `183` | `985·34` |

Honest: two data points do not give a selection rule (`194` is not a partner of `1325`'s triple, so the
naive "realized root ties to the larger partner" fails at `1325`).  The value is (i) more ∅-axiom verified
cases, (ii) explicit instances to test any future selection principle against.

## D. What a successful attack must now overcome (recorded for the next attempt)

The locality obstruction (B) tells us the shape of any argument that could cross the wall: it must be
**global / cross-`c`** (it must use the descent trajectory, not fixed-`c` data), which is precisely the
continuant/Christoffel route (`G191` E2–E5, oriented run-lengths) and the classical stable-norm
(`H¹(torus)`, cross-`c`).  A *forced* (local) argument provably cannot do it — so direction (2) as a
pure-forcing attack is closed; its honest residue is the obstruction statement (B) plus the verified cases
(C).  The live cross-`c` directions remain `G193` Part 3 #1 (continuant bridge) and #3 (the `2^(ω−1)` count
theorem); #4 (cohomology δ over the ω primes) is the one *local* object that is genuinely cross-suborbit
and so might evade the locality obstruction — flagged as the speculative exception.

### Pointers
- forced tower (maximal reduction): `Real213/Markov/SternBrocotMarkov` §20–§26 (`windowRealizedUnique_of_orbit`,
  `markov_max_unique_of_orbit`, `window_excludes_partner`, `root_orbit_inj`)
- new case: `markov_max_unique_985_via_orbit` (and `markov_max_unique_1325_via_orbit`)
- companions: `G193` (axiom attack map), `G192` (Raw/Lens boundary), `G191` (continuant program)
