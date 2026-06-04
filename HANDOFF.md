# Session Handoff — 2026-06-04g (Markov — ★ UPPER-FOLD PATTERN, five levels; full ω=2 structural reduction, §20–§24)

## Branch `claude/markov-uniqueness-0R0Ut` — pushed, clean.  `Real213/SternBrocotMarkov` **100 PURE**.

## ★★★ NEW (§24): orbit-injectivity — the unit-root group acts FREELY
The last structural piece for `ω=2`.  A `√(−1)` root `u` is a unit (inverse `c−u`), so multiplication
by a unit-root is cancellable ⟹ the §21 group acts **freely** on the root set.
- **`unit_cancel_of_inv`** `(u·s≡1) : a·u≡b·u → a≡b` (multiply by inverse `s`; no subtraction).
- **`unit_cancel`** `(1<c)(gcd u c=1) : a·u≡b·u → a≡b` (inverse via `modBezout`).
- **`root_inverse`** `(1<c)(u≤c)(u²+1≡0) : u·(c−u) ≡ 1` (the explicit unit, from `u·(c−u)+(u²+1)=u·c+1`).
- **`root_orbit_inj`** `e·u≡u → e≡1`;  **`root_orbit_inj_neg`** `e·u≡(c−1)·u → e≡c−1`.
- **Consequence (with §21–§23)**: `2^ω` unit-roots → `2^ω` *distinct* roots (free action) → window's
  `⟨−1⟩`-transversal keeps `2^{ω−1}` distinct windowed roots, each a distinct `±`-suborbit.  So the
  **windowed-root count is settled exactly** (`= 2^{ω−1}`); the ONLY remaining Markov question is
  realizability (which suborbit carries a triple).  `WindowRealizedUnique` (§18) = "exactly one does."

### The five-level fold (the user's predicted recursion, all ∅-axiom)
```
§20  window = σ-transversal                       involution σ(u)=c−u
§21  σ ∈ SqrtUnity, root set = torsor              the group of involutions
§22  SqrtUnity = ∏ (per-prime ± folds)             product of folds
§23  that product is inhabited beyond ±1 (CRT)     the product is non-trivial (ω=2)
§24  the group acts freely (unit cancellation)     orbits are faithful ⟹ count = 2^{ω−1}
```
**Full structural reduction of `ω=2` Markov uniqueness is now ∅-axiom.**  The residual — *which* of the
`2^{ω−1}` suborbits is Markov-realized — is the genuine open Frobenius content, and it is exactly what
`WindowRealizedUnique` isolates.  Everything *around* it (root-count, group, freeness, existence) is closed.

## ★★★ (§23): nontrivial unit-root EXISTENCE — open content closed for ω=2
The CRT *existence* half of the open Markov content, now ∅-axiom.
- **`nontrivial_unit_root_exists`** `(3≤m)(3≤n)(gcd m n=1) : ∃ e, SqrtUnity (m·n) e ∧ e≠1 ∧ e≠m·n−1`.
  Construction `e = 1 + m·t`, `t ≡ (n−2)·m⁻¹ mod n` (`m⁻¹` from `inverse_of_coprime`/`modBezout`):
  `e ≡ 1 mod m`, `e ≡ −1 mod n` — the CRT product `(1,−1) ∈ Z/m × Z/n`, non-diagonal ⟹ `≠ ±1`.
  `sqrtUnity_lift` (§22) certifies `e²≡1 mod c`.
- **Consequence**: `SqrtUnity c ⊋ {±1}` *unconditionally* at every two-factor composite ⟹ the `2^ω`
  root explosion is real, phantoms genuinely exist ⟹ Markov uniqueness there **cannot** come from
  root-counting; it must come from realizability (`WindowRealizedUnique`, §18).  This formally locates
  the open content: it is *exactly* the phantom-elimination `WindowRealizedUnique` supplies.
- **`aux_1_add_sub2`, `aux_pred_mul_mod`** : the two ∅-axiom Nat arithmetic helpers (via `Nat.le.dest`
  / `succ_pred` / `add_mul_mod_self_pure`; no `omega` — `omega` leaks propext+Quot.sound).

### Remaining open content (now precisely ONE thing)
With existence done, the only piece left for `ω=2` uniqueness is the **orbit-injectivity**:
`e·u ≡ ±u mod c ⟹ e ≡ ±1` (cancel by the unit `u`; `u²≡−1` makes `u` invertible via `modBezout`).
That + existence = "the window's two reps are the two `±`-suborbits, and only the diagonal one is
Markov-realized" — i.e. it reduces `WindowRealizedUnique` to a *single* realizability check per
phantom orbit.  Engine fully ready (`mul_dvd_of_coprime`, `inverse_of_coprime`, `sqrtUnity_acts_on_root`).

## ★★★ (§22): the fold is a product of folds — `SqrtUnity` factors over coprime components
Third level of the recursion: the §21 unit-root group is *multiplicative* across coprime factors, so
the composite fold IS a product of the per-prime-power `±` folds — the exact mechanism by which `ω`
controls the phantom count.
- **`mul_dvd_of_coprime`** `(1<n)(gcd m n=1)(m∣k)(n∣k) : m*n ∣ k` — the previously-MISSING reusable
  ∅-axiom primitive, via `euclid_of_coprime` (MarkovPrimeFactor).
- **`sqrtUnity_lift`** `(1<m)(1<n)(gcd=1)(e²≡1 mod m)(e²≡1 mod n) : SqrtUnity (m*n) e` — so
  `SqrtUnity c ⊇ ∏ {±1 mod pᵢ}`: `ω` independent `±` folds → `2^ω` unit-roots → window's `⟨−1⟩`
  transversal keeps `2^(ω−1)` → all but one phantom.
- **`sqrtUnity_1325_nontrivial`** : `SqrtUnity 1325 476 ∧ 476∉{1,1324}` — `SqrtUnity ⊋ {±1}` concrete.
- **`phantom_is_unit_root_image_1325`** : `476·507 ≡ 182 mod 1325` (507,182 both √−1) — the nontrivial
  unit-root carries the realized root 507 to the phantom 182; same full-group orbit, different
  `±`-suborbits = exactly why the window can't separate them.  `sqrtUnity_acts_on_root` made arithmetic.

### Remaining open content (now sharply isolated)
The genuine open Markov piece = **nontrivial-unit-root existence for general `ω≥2`** (CRT construction:
`e ≡ 1 mod m`, `e ≡ −1 mod n`, then `sqrtUnity_lift`).  Engine ready (`mul_dvd_of_coprime` +
`inverse_of_coprime`/`modBezout`); what's left is the CRT *existence* of `e` (build `e = 1 + m·t` with
`t ≡ −2·m⁻¹ mod n`) + the orbit-injectivity `e·u ≡ ±u ⟹ e ≡ ±1` (cancel by the unit `u`, since
`u²≡−1` makes `u` invertible).  Everything *structural* around it is now ∅-axiom.

## ★★★ (§21): the next fold — root set is a torsor under the unit-root group
Templatizing §20 hits the next wall (ω≥2 composites leave phantom roots).  The wall is *again a fold*,
one level up: the `√(−1)` root set is a **torsor under the square-root-of-unity group**, and §20's `±`
involution `σ` is that group's distinguished order-2 element `c−1 ≡ −1`.
- **`SqrtUnity c e := (e*e)%c = 1`** — the acting group.
- **`one_sqrtUnity` / `neg_one_sqrtUnity`** : `{1, c−1} ⊆ SqrtUnity` (always present).
- **`neg_one_mul_is_neg`** : `(c−1)·r + r ≡ 0` (so `c−1 = −1` exactly; with `neg_one_sqrtUnity` this
  identifies `σ = ·(c−1)`, the §20 fold, as one element of the group).
- **`sqrtUnity_mul`** : closed under mod-multiplication (it IS a group).
- **`sqrtUnity_acts_on_root`** : `e²≡1 ∧ (r²+1)≡0 ⟹ ((e·r)²+1)≡0` — the torsor action;
  `neg_root_is_root` (§20) is the `e=c−1` instance.
- **Reading**: prime power ⟹ `SqrtUnity={±1}` ⟹ each orbit is one `±`-pair ⟹ window unique (Button,
  §13).  `ω≥2` ⟹ `SqrtUnity ⊋ {±1}` ⟹ orbits exceed `±`-pairs ⟹ window leaves `2^(ω−1)` reps = the
  phantoms.  `WindowRealizedUnique` is the second constraint collapsing them.
- **Next thread**: the still-open piece is the nontrivial-unit-root *existence* for `ω≥2` (needs CRT /
  Bezout — check if `Padic`/`ModArith` already has a pure CRT) + the "phantom is a different `σ`-orbit"
  injectivity (needs `e·u ≡ ±u ⟹ e ≡ ±1`, i.e. cancel by the unit `u`).  That's the genuine open
  content; everything structural around it is now ∅-axiom.

## ★★★ (§20): the upper-fold pattern — window = ±-fold transversal
The template (§18) is **not** a number-closing device; it IS the generalization insight of the
**upper-fold pattern** (per Mingu's correction).  §20 makes that explicit:
- **`window_excludes_partner` (c r) (2r<c) : c < 2(c−r)** — a windowed root has its ±-partner `c−r`
  *outside* the window.  Proved omega-free (omega leaks propext+Quot.sound) via `NatHelper.add_sub_of_le`.
- **`window_fold_transversal` (c r) (r<c) (root) (2r<c) : ((c−r)²+1)%c=0 ∧ ¬(2(c−r)<c)** — bundles
  `neg_root_is_root` (σ(u)=c−u preserves the root set) with `window_excludes_partner`: the window
  (0,c/2) is a **transversal** of the ± involution σ, exactly one rep per {u, c−u} pair.

  **Markov uniqueness = fold by σ (the window) + the realized fold-point is unique
  (`WindowRealizedUnique`).**  Same fold the repo reads as the unit's two faces
  (`HyperbolicEllipticTrace`, the Δ-sign φ/π split §14), 0/∞ as one reciprocal hole
  (`ZeroInfinityHole`), and the ±/Cassini sign (`DetSpectrumPoles`).
- Dropped a redundant `0<r` hypothesis from both (assume-nothing).

## ★★★ composite-`c` uniqueness, beyond Button (§16–§19)
- **First three composite Markov numbers closed ∅-axiom** (all with the `2^ω=4` root explosion where
  `SqrtNegOneTwoRoots` FAILS): `markov_max_unique_610` (2·5·61=F₁₅), `markov_max_unique_985` (5·197),
  `markov_max_unique_1325` (5²·53).  Plus `markov_max_unique_65` (non-Markov, vacuous).
- **`window_realized_unique_of_one_phantom`** (§19): windowed roots `⊆ {P,Q}` with `P` phantom ⟹
  `WindowRealizedUnique c`.  Reduces each `ω=2` composite to two `O(c)` `decide`s (windowed-root set
  + the phantom's `∀b<c ¬markovEq`).  New composite = supply `(c, P, Q)` + two decides.
- **The template `markov_max_unique_of_window_realized_unique`** (§18): `5≤c ∧ WindowRealizedUnique c
  ⟹ MarkovMaxUnique c` — the genuine reduction of composite-`c` uniqueness to **phantom elimination**,
  as a ∅-axiom theorem.  `WindowRealizedUnique` = only the *realized* windowed `√(−1)` roots need be
  unique (strictly weaker than `SqrtNegOneTwoRoots`).  `window_realized_unique_of_sqrtNegOne` makes
  Button a special case.
- Plumbing: `mNode_max` (mediant is strict max, §16), `node_recovery_nat` ((r·m_l)%c=m_r ℕ, §17, via
  pure `mod_eq_of_ofNat_dvd_sub` + main's `ofNat_sub_ofNat`), `node_realized` (every node residue is
  realized).
- 1325 closure uses the repo's existing `markov_composite_separation` (182 phantom / 507 realized)
  + a feasible `decide` that windowed roots ⊆ {182,507}.  Correction to earlier note: the *naive*
  `∀u₁∀u₂` decide is `c²`-infeasible, but the windowed-roots `decide` is `c` (feasible), and the
  realize-uniqueness is closed structurally via the phantom data.
- §14 (hyperbolic disc, Markov tree on φ-face of SL₂) + §15 (`det2 = DetN.det` at n=2, + 2×2
  multiplicativity back to general `DetN`) — concept imports from the main merge.

### Path to MORE composite Markov numbers
Each composite Markov number `c` closes the same way: `decide` the windowed-root set (feasible, `c`)
+ supply the phantom roots' `∀b<c ¬markovEq` (feasible, `c` per root) → `WindowRealizedUnique c` →
template.  `610 = 2·5·61` is the next; the bottleneck is producing the `markov_composite_separation`-
style phantom data per `c` (mechanical).

## ★ EARLIER 2026-06-04: BUTTON'S THEOREM CLOSED, ∅-axiom

## ★★★ MILESTONE: `Real213/SternBrocotMarkov` **63 PURE** — prime-power uniqueness DONE
The whole chain is now closed, fully ∅-axiom (`#print axioms` clean):
- **`markov_max_unique_tree`** (§13): `5 ≤ c ∧ SqrtNegOneTwoRoots c ⟹ MarkovMaxUnique c`.  Two
  ordered triples at `c` are both tree nodes (`reverse_bridge` §12); each node's residue is the
  unique windowed `√(−1)` mod `c` (`node_window_nat` = `markov_window` §9 + `markovNum_dvd_res_sq_succ`
  §5 converted ℤ→ℕ, + `root_unique_below_half`); equal residues ⟹ equal slopes (same `c`) ⟹ equal
  nodes (`slope_path_inj` §11) ⟹ equal triples.
- **`markov_prime_pow_unique`** (§13): `c = p^(k+1)` odd prime power, `5 ≤ c` ⟹ `MarkovMaxUnique c`
  (via `sqrtNegOneTwoRoots_prime_pow`).  **Button's theorem — the infinite prime-power family of the
  Markov uniqueness conjecture — fully ∅-axiom.**
- ℤ→ℕ assembly helpers (`int_toNat_lt`, `nat_dvd_of_ofNat_dvd`, `node_window_nat`, `node_data`) all
  pure; avoided propext leaks (`Nat.mul_mod_right`→`NatHelper.mul_mod_right`, `Nat.add_left_cancel`,
  `Nat.sub_add_cancel`, `Nat.mul_assoc`, core `List` lemmas).

### Full architecture (all ∅-axiom, in `SternBrocotMarkov`):
§1 det-1 Stern-Brocot tree · §2 Markoff-matrix tree (det=1, Frobenius, Vieta) · §3 generates Markov
triples · §4 positivity · §5 `u²≡−1` · §6 Frobenius residue cross + recovery · §7–§8 strict slope
monotonicity (both halves) · §9 window `0<u<m/2` · §10 forward bridge (tree = Markov tree) · §11
**global slope injectivity** · §12 **reverse bridge** · §13 **Button's theorem**.

### What remains OPEN (correctly untouched): composite `c` with ≥2 prime factors ≡1 mod 4
`SqrtNegOneTwoRoots` *fails* there (≥4 roots) — the genuinely open zone of the conjecture.  The tree
machinery (`markov_max_unique_tree`) is general; only the `SqrtNegOneTwoRoots` input is missing for
composite `c`.  Possible future: `markov_max_unique_of_same_pair_injective` interface, or pushing the
window/injectivity to handle multiple ±pairs.

## ★ EARLIER (this marathon): §12 reverse bridge (61 PURE)

## ★ LATEST: `Real213/SternBrocotMarkov` **61 PURE** — §12 reverse bridge (objective #1 DONE)
- **`reverse_bridge`**: every ordered Markov triple `(a,b,c)`, `1≤a≤b≤c`, `5≤c`, is a matrix-tree
  node — `IsNode a b c ∨ IsNode b a c`.  By Vieta descent (`reverse_of_fuel`, fuel=`c`): base `c=5`
  ↦ root `(1,2,5)` (`markov_max_unique_5`); `c≥6` descend to parent `{a,b,3ab−c}` (max `b≥5` via
  `markov_mid_ge_5` — bounded `decide` `markov_small_mid`), recurse, re-ascend via `descent_step`.
- Scaffolding: `IsNode`, `node_true_child`/`node_false_child` (Vieta up-moves, `∃d + jump-eq`,
  no Nat subtraction), `isNode_root`, `descent_step`.
- ∅-axiom care: used pure `add_left_cancel_pure`, `NatHelper.sub_add_cancel`; avoided
  propext-leaking `Nat.add_left_cancel`/`sub_add_cancel`/`mul_assoc`.  All MarkovUniqueness
  descent lemmas verified pure.

### ★ FINAL ASSEMBLY remaining → `SamePairInjective` → prime-power `MarkovMaxUnique`
Both hard pieces are now in hand: **`slope_path_inj`** (§11, global injectivity) + **`reverse_bridge`**
(§12).  `SamePairInjective c` (`MarkovInjectivity`) is: two ordered triples at `c` with recovery
residues `u_i` (`u_i<c`, `(u_i·b_i)%c=a_i`) in the same ±pair ⟹ equal.  Assembly plan:
  1. `reverse_bridge` → each triple is node `p_i`; `(m_l,m_r)={a_i,b_i}`, `m_t=c`.
  2. **Connect residues** (the remaining plumbing): the node's Int residue `r_i = markovRes p_i`
     satisfies `r_i² ≡ −1` (`markovNum_dvd_res_sq_succ`) and `r_i·m_l ≡ m_r` (`markovRes_recovery_dvd`),
     windowed `0<r_i, 2r_i<c` (`markov_window`) — convert these Int-divisibility facts to Nat `% c`.
     Then the given `u_i ∈ {r_i, c−r_i}` (modular inverse, using coprimality + `r²≡−1`).
  3. `u₁,u₂` same ±pair + each `u_i∈{r_i,c−r_i}` ⟹ `r_1,r_2` same ±pair; both windowed ⟹
     `root_unique_below_half` ⟹ `r_1=r_2` ⟹ `slopeEq (mNode p_1)(mNode p_2)` (same `c`) ⟹
     `slope_path_inj` ⟹ `p_1=p_2` ⟹ same node ⟹ sorted `(a_i,b_i)` equal.
  Then `markov_max_unique_of_same_pair_injective` (DONE) ⟹ `MarkovMaxUnique`;
  `markov_prime_pow_unique_of_same_pair_injective` (DONE) ⟹ Button's family.
The remaining work is step 2's Int↔Nat modular conversion (substantial but well-scoped plumbing) —
the conceptual cruxes (injectivity, reverse bridge) are both closed.

## ★ EARLIER 2026-06-03e: GLOBAL SLOPE INJECTIVITY (§11, 54 PURE)

## ★ LATEST: `Real213/SternBrocotMarkov` now **54 PURE** — §11 global slope injectivity
**The genuine crux that the "reverse-bridge + window ⟹ SamePairInjective" chain GLOSSED OVER.**
The window (§9) only fixes each node's residue within its *own* `c`; it does NOT give that two
distinct triples at the *same* `c` are equal.  That needs **node ↦ slope `u_t/m_t` injective across
the whole tree** (Stern-Brocot ordering).  Now proven:
- `slopeLt`/`slopeLe` (cross-multiplied) + transitivity family (`slope_trans`, `slope_le_lt_trans`,
  `slope_lt_le_trans`) on the §9 Int toolkit (+ `mul_pos`, `mul_lt_mul_right`, `lt_trans`,
  `lt_irrefl_int`).
- `slope_nest`: interval bounds nest in slope as the tree deepens (left rises, right falls).
- `subtree_between`: every node in `t`'s subtree (`s ++ t`) lies STRICTLY between `t`'s bounds;
  `subtree_true_lt`/`subtree_false_gt` are the directional forms.
- `slope_sep`: distinct paths (shared deep suffix) ⟹ separated slopes, by length-fuel induction
  peeling shallow ends.  Needed **pure** List helpers (`eq_nil_or_concat`, `concat_ne_nil`,
  `append_singleton_cancel`) — core `List` lemmas leak propext.  Decidable-eq split avoids Classical.
- **`slope_path_inj`**: `slopeEq (mNode p) (mNode q) ⟹ p = q`.  ∅-axiom verified.

### Honest status of the objective (reverse bridge + SamePairInjective)
The objective's 3-step chain had a real gap at step 2 (global injectivity) — now FILLED.  Two pieces
remain for prime-power `MarkovMaxUnique`:
  1. **Reverse bridge** (objective #1, NOT yet done): every ordered Markov triple with `c ≥ 5` is a
     matrix-tree node.  Route: `markov_ordered_reachable` (DONE, abstract descent) → invert
     `MarkovReachable`/descent to a Stern-Brocot path.  Caveat: indexing offset (tree roots `(1,2,5)`,
     `MarkovReachable` roots `(1,1,1)`); needs ℤ↔ℕ (`toNat`, §10 helpers) + descent-to-path.
  2. **Assembly**: two triples at `c` ⟹ (reverse bridge) two nodes `p,q`; same windowed residue (via
     `root_unique_below_half`, the residues are equal) ⟹ same slope ⟹ (`slope_path_inj`) `p = q`
     ⟹ same triple ⟹ `SamePairInjective`.  Then `markov_prime_pow_unique_of_same_pair_injective`
     (DONE) closes Button's family.
The crux (injectivity) being done de-risks the remainder substantially — the assembly is now mostly
plumbing once the reverse bridge lands.

## ★ EARLIER 2026-06-03d: forward bridge (matrix tree = Markov tree, 48 PURE)

## ★ LATEST: `Real213/SternBrocotMarkov` now **47 PURE** — §10 forward bridge
- **§10 `mInterval_reachable`**: every matrix-tree node's `(2,1)`-entry triple `(m_l,m_r,m_t)`, as
  `Nat`, is `MarkovUniqueness.MarkovReachable` (root `(1,1,1)` + Vieta jumps + swaps).  **The Markoff
  matrix tree realises exactly the Markov tree.**  By induction: each L/R mediant step is a Vieta
  jump (`markoff_vieta(_R)` + entry-shape ⟹ `m_t' = 3·m_i·m_j − m_k`), matched to the `jump`
  constructor after reordering by `swap`s.  Bridges ℤ→ℕ via `Int.toNat` (entries positive): pure
  `toNat_of_nonneg`/`toNat_add`/`toNat_mul` + `jump_eq_toNat` (all ∅-axiom).
- Consequence: tree nodes now inherit ALL of `MarkovUniqueness`'s reachable-triple theorems
  (`markov_reachable_coprime`, `markov_reachable_no_3mod4_factor`, `markov_reachable_neg_one_qr`, …).

### Remaining gap to `SamePairInjective` — now precisely the REVERSE bridge
`markov_ordered_reachable` (already in `MarkovUniqueness`) gives: every ordered triple is
`MarkovReachable`.  §10 gives: every matrix-tree node is `MarkovReachable`.  The missing piece is the
**reverse of §10**: every `MarkovReachable` triple (with max ≥ 5) is a matrix-tree *node* (so the
window/monotonicity §7–§9 applies to it).  **Caveat — indexing offset**: the matrix tree roots at
`(1,2,5)` (node `[]`), while `MarkovReachable` roots at `(1,1,1)`; the small triples
`(1,1,1),(1,1,2)` are NOT matrix-tree nodes.  So the reverse bridge is "every MarkovReachable triple
with max ≥ 5 is a tree node" — provable by induction on the derivation but needs care at the small
base triples + inverting jumps/swaps to a Stern-Brocot path.  This is the crux that remains.
With it: window-injectivity (§9) + reverse bridge ⟹ `SamePairInjective` ⟹ `MarkovMaxUnique` (via the
DONE `markov_max_unique_of_same_pair_injective`); prime powers ⟹ Button's infinite family.

## ★ EARLIER 2026-06-03c: tree-side of Zhang Lemma 2 COMPLETE (§9 window, 46 PURE)

## ★ LATEST: `Real213/SternBrocotMarkov` now **46 PURE** — §9 window added
- **§9 residue window** (`markov_window`): every tree node satisfies `0 < u_t < m_t/2` — the
  canonical Markov window of `MarkovInjectivity.root_unique_below_half`.  Root bounds have slopes
  `0/1`, `1/2`; strict monotonicity (§7–§8) confines every node strictly between.  Proof:
  `mInterval_window` (closed window `0 ≤ u ≤ m/2` on **both** bounds, by induction; the node's strict
  window from `node_window_of_bounds` weakens to propagate as a bound).
- Added a **pure ℤ strict-order toolkit** (all private, ∅-axiom): `pos_of_mul_pos_right`
  (positive-factor cancellation, by case analysis on `z,k` — no trichotomy), `lt_of_mul_lt_mul_right`,
  `mul_le_mul_right`, `lt_two_mul`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_of_lt`, `nonneg_add`,
  `pos_sub_of_lt`/`lt_of_pos_sub`, `ofNat_succ_pos`, `zero_le_of_nonneg`/`nonneg_of_zero_le`.  All on
  the `Int.NonNeg` backbone (`subNatNat_of_le`, `mul_nonneg`).  Reusable.

### ★ TREE-SIDE OF ZHANG LEMMA 2 IS COMPLETE.  Every tree node's residue `u_t`:
  - squares to `−1` mod `m_t` (§5 `markovNum_dvd_res_sq_succ`),
  - recovers the partner Markov number `u_t·m_l ≡ m_r` (§6 `markovRes_recovery_dvd`),
  - has strictly monotone slope `u_l/m_l < u_t/m_t < u_r/m_r` (§7–§8),
  - lies in the canonical window `0 < u_t < m_t/2` (§9 `markov_window`).

### ★ THE ONE REMAINING GAP to `SamePairInjective` (= the open conjecture core): SURJECTIVITY
`SamePairInjective c` is over **arbitrary Nat triples** at max `c`.  The tree→data direction is done;
the missing piece is **surjectivity / Frobenius completeness**: every ordered Markov triple `(a,b,c)`
appears on the tree (as some node's c-entry triple `(m_l,m_r,m_t)`).  Classical proof = **Vieta
descent**: replace max `c` by `3ab−c < c`, repeat to reach `(1,1,1)` = root; each step = a tree
parent.  `MarkovUniqueness.lean` already has descent infrastructure (`markov_ordered_reachable`,
`markov_descent`-style, `markov_up_jump`) over abstract Nat triples — the task is the **bridge**:
connect the matrix tree's `markovNum`/triple to the abstract-triple descent (show `markovNum` ranges
over exactly the Markov numbers, surjectively).  With surjectivity + window-injectivity (now in
hand), `SamePairInjective` closes ⇒ `markov_max_unique_of_same_pair_injective` (DONE) closes
`MarkovMaxUnique`; for prime powers, `markov_prime_pow_unique_of_same_pair_injective` (DONE) gives
Button's infinite family.

Next session: the surjectivity bridge (tree `markovNum` ↔ abstract Markov triples via Vieta descent).
Inspect `MarkovUniqueness` reachability lemmas first; the bridge may be short given the descent is
already there.

## ★ EARLIER 2026-06-03: full Zhang Lemma 2 monotonicity (§7–§8, 43 PURE)

## ★ LATEST: `Real213/SternBrocotMarkov` now **43 PURE** — §7–§8 added
- **§7 right-half monotonicity** (`markov_node_slope_lt_right`): `u_t·m_r < u_r·m_t` — the node's
  residue slope is strictly below the right bound's.  From `markovRes_cross` (= `m_l`) + `m_l ≥ 1`.
  Int bridge `lt_of_sub_eq_of_one_le`.
- **§8 left identity + full monotonicity**:
  - `markoff_res_vieta` (L) / `markoff_res_vieta_R` (R): the **residue Vieta recurrence** — `u = d−c`
    satisfies the *same* Cayley–Hamilton recurrence as the number `c` (because it's linear).
  - `bound_res_identity` (generic, needs only right bound's shape): `m_l·u_r − m_r·u_l = 3 m_l m_r − m_t`.
  - **`markovRes_cross_left`**: `u_t·m_l − u_l·m_t = m_r` — the tree-specific left Frobenius identity
    (the deferred mirror), **proven by coupled tree induction**: R-step via IH; L-step via
    `3·m_l·(IH) − (bound_res_identity)`.  Multipliers found by sympy.
  - **`markov_node_slope_gt_left`**: `u_l·m_t < u_t·m_l` (left half).  
  **⇒ FULL Zhang Lemma 2 on the tree**: `u_l/m_l < u_t/m_t < u_r/m_r` — the mediant residue slope lies
  *strictly between* the two interval bounds.  The core monotonicity is DONE.

### ★ IMMEDIATE NEXT: the window `0 < u_t < m_t/2` (clean corollary, plan ready)
Root bounds have slopes `0/1` and `1/2`; monotonicity keeps every node strictly between ⇒ window.
Proof plan (carry invariant `W(M) := 0 ≤ M.d−M.c ∧ 2(M.d−M.c) ≤ M.c` on **both** bounds):
  - base: genL `u=0`, genR `u=1,m=2` both satisfy `W`.
  - L/R-step: node satisfies `W` from `markov_node_slope_gt_left` (+ `0 ≤ u_l` ⇒ `0 < u_t`) and
    `markov_node_slope_lt_right` (+ `2u_r ≤ m_r` ⇒ `2u_t < m_t`); node's strict `W` ⇒ non-strict `W`,
    so it propagates as a bound.
  - **Needs new pure Int helpers**: `le_zero_or_one_le : ∀ d:Int, d ≤ 0 ∨ 1 ≤ d` (cases on
    ofNat/negSucc); `mul_nonpos_of_nonpos_of_pos`; `lt_of_mul_lt_mul_right : a·c < b·c → 0 < c → a < b`
    (and the special `pos_of_mul_pos_right`).  ~40–50 lines; the only reason it wasn't done this
    session (budget).  Build these in `Meta/Int213/Bound.lean` (reusable) or locally.
Then connect the windowed tree residue to `MarkovInjectivity.root_unique_below_half`'s `(0,c/2)`
window — the tree residue IS the canonical windowed root.

## ★ EARLIER THIS DAY: `Real213/SternBrocotMarkov` 27 → 37 PURE (§4–§6)
The Markoff-matrix tree carrier is fully wired for the residue analysis.  Earlier this marathon:
`mInterval`/`mNode` (interval-mediant tree, NOT word products), `det2_mul`, `mInterval_det`,
`mNode_det1`, `markoff_frobenius`, `markoff_vieta(_trace)(_R)`, `mInterval_shape` (tr=3c keystone),
`mInterval_markov` (the tree generates Markov triples).  **New §4–§6 this iteration:**

- **§4 positivity** (`posMat`, `posMat_mul`, `mInterval_pos`, `mNode_pos`, `markovNum_pos`): every
  bound + node matrix has all four entries `≥ 1` (tree induction; `mul` preserves it).  Pure Int
  positivity helpers (`one_le_mul`, `one_le_add_nonneg`, `nonneg_of_one_le`, `sub_zero_int`) via the
  `Int.NonNeg`/`add_nonneg`/`mul_nonneg` backbone.  The monotonicity-sign prerequisite.
- **§5 `u_t² ≡ −1 (mod m_t)`** (`markovRes_sq`, `markovNum_dvd_res_sq_succ`): one-shot ring identity
  `u_t²+1 = (m_t+d−b)·m_t` from `det=1` + entry-shape.  The `SqrtNegOneTwoRoots` congruence on every
  node — each residue is an honest √(−1) mod its Markov number.
- **§6 Frobenius residue cross + recovery**:
  - `markoff_frobenius_res` (generic det-1 identity) + `markovRes_cross`: `u_r·m_t − u_t·m_r = m_l`.
    (The mirror `u_t·m_l − u_l·m_t = m_r` is **tree-specific**, 54/2000 on random det-1 matrices —
    needs induction, deferred.  Confirmed by sympy/random search.)
  - **`markovRes_recovery_dvd`**: `m_t ∣ (u_t·m_l − m_r)`, i.e. `u_t·m_l ≡ m_r (mod m_t)` — the
    `SamePairInjective` recovery congruence, derived **purely by modular arithmetic** from §5+§6
    (multiply `u_t·m_r ≡ −m_l` by `u_t`, use `u_t² ≡ −1`).  NO tree induction.  INSIGHT: the recovery
    is free once you have the √(−1) congruence + the one generic Frobenius residue identity.

**Net**: every tree node carries the full `(root, recovery)` data of `SamePairInjective` — squares
to −1 mod `m_t` AND recovers the partner Markov number.  This is the *tree → data* direction.

### Precise remaining gap to `SamePairInjective` (the open conjecture core)
`SamePairInjective c` (`MarkovInjectivity.lean`) is over **arbitrary Nat triples** at max `c`.  Two
genuinely-hard pieces remain, both tree-specific (NOT generic ring identities — verified):
  1. **Surjectivity** — every Nat Markov triple with max `c` is on the tree (Frobenius completeness).
  2. **Entry ordering `c ≤ d ≤ a ≤ b`** (⟹ window `0 < u_t < m_t/2` ⟹ residue injective on tree).
     Window `0<u_t` ⟺ `c<d`; `2u_t<m_t` ⟺ `d<a` (via `a+d=3c`).  NOT generic (49/59 det-1+shape+pos
     matrices violate it — the bounds violate, nodes satisfy) → needs the **coupled-invariant tree
     induction** on the bounds (à la `mInterval_shape`), the "[subtle: inequalities]" step.  Find the
     bound-invariant numerically first.

Next session: attempt the §7 ordering induction (coupled invariant on interval bounds), then window
→ `SamePairInjective` on the tree.  Surjectivity is the separate hard half.

---

# Session Handoff — 2026-06-02 (Markov uniqueness marathon)

## Branch
`claude/markov-uniqueness-0R0Ut` — pushed.  Working tree clean.  **`origin/main` re-merged** (the
Cassini/orbit/depth thread — `CassiniUnimodular`, `CassiniDepthFloor`, `SecondCasoratian`,
`FibCassiniNat`; `CayleyDickson/.../UnitsToModular`; `ring_intZ`/`PolyIntM`).  HANDOFF kept ours.

## ★ NEW (this session): `Real213/MarkovCassiniBridge` (3 PURE) — Markov spine ↔ main's Cassini
Using merged-main's `CassiniUnimodular` (`det_closed`: `D(n)=qⁿ·D(0)`, the `q=±1` floor) +
`FibCassiniNat.fib_cassini_norm`, the Markov–Fibonacci spine reads the Cassini unimodular dichotomy:
- `markov_spine_sqrt_neg_one_cassini` (`q=−1`): `fib(2n+3) ∣ fib(2n+2)²+1` because
  `fib(2n+2)²+1 = fib(2n+1)·fib(2n+3)` IS `fib_cassini_norm` — the √(−1)-residue is the `q=−1`
  Casoratian value.
- `markov_fib_second_cassini` (`q=+1`): `fib(2n+1)·fib(2n+5) = fib(2n+3)²+1` — the spine's
  index-gap-2 Cassini is the conserved unit (`det_closed` at `q=1` for `s(n+2)=3s(n+1)−s(n)`).
- `markov_spine_cassini_dichotomy` bundles them; both reduce to `fib_cassini_norm`.

## ★ NEW (this session): `Real213/MarkovModularBridge` (2 PURE) — Markov pair = `S`'s eigenvector
Realizes the HANDOFF "213-native conjecture" via merged-main's `ModularElliptic.S` (= Gaussian
unit `i`, `UnitsToModular.repI i = S`) + `ring_intZ`:
- `markov_pair_eigen` (∅-axiom `ℕ`): for a Markov triple, the recovery residue `u=(a·b⁻¹)%c` has
  `(u·b)%c = a` (recovery) and `(u·a+b)%c = 0` (neighbor congruence `a²+b²≡0` + Euclid via
  `b·(u·a+b)=c·(a·q+(3ab−c))`).  These ARE `S·(a,b) ≡ u·(a,b) (mod c)`.
- `S_eigenvector_of_dvd` (∅-axiom `ℤ`, `ring_intZ`): the abstract criterion — `c∣(u·a+b) ∧
  c∣(u·b−a) ⟹ S·(a,b) − u·(a,b) ≡ 0` (`S=[[0,-1],[1,0]]`).
So the √(−1)-residue indexing a Markov number is the eigenvalue of the Gaussian unit `i = S` on the
Markov pair `(a,b)` mod `c`.  (The only formality between the two is the Nat→Int dvd cast.)

## ★ NEW (this session): `Real213/MarkovInjectivity` (9 PURE) — the injectivity analysis
After a literature deep-dive (Zhang 2007, Lang–Tan, Baragar, Button, Aigner), the open locus is
recalibrated.  Reduction: `MarkovMaxUnique c ⟸ SqrtNegOneTwoRoots c ∧ residue-map-injective`.
- **Zhang Lemma 4 — DONE**: `root_unique_below_half` (with the 2-root property, ≤1 root of `x²≡−1`
  in `(0,c/2)`; the `x+y=c` branch dies when `2x,2y<c`).  `root_unique_below_half_prime_pow` uses
  primality ONLY via `sqrtNegOneTwoRoots_prime_pow` — the single primality lock of Button's theorem.
- **Parallel reduction** (`markov_same_root_parallel`, `coprime_cross_eq`, `markov_eq_of_cross`):
  same-root triples are parallel mod `c`; coprime+exact-parallel ⟹ equal.
- **Dead end recorded**: `|a₁b₂−a₂b₁| < c` is FALSE — Frobenius's identities make the
  cross-determinant a neighbour Markov number (≈c).  No size bound closes it.
- **Open content** is *root-counting* (Markov-realisability of the `2^{ω−1}` window-roots) for
  composite `c`, ω≥2 — NOT the injectivity of `triple↦root`.
- **★ Capstone reduction** (`markov_max_unique_of_same_pair_injective`): `MarkovMaxUnique c ⟸
  SqrtNegOneTwoRoots c ∧ SamePairInjective c` — the exact Frobenius/Aigner reduction, both inputs
  honest.  **`markov_prime_pow_unique_of_same_pair_injective`**: for `c=p^(k+1)`, uniqueness ⟸
  `SamePairInjective` ALONE (root-count discharged) — **Button's prime-power unicity (infinite
  family) reduced to the single residue-injectivity input** `SamePairInjective` (= Zhang Lemma 2).
- **Triple determined by two largest entries** (`markov_same_mid_eq`): two ordered triples sharing
  `(b,c)` coincide (`a` = the unique root `≤ b` of the Vieta quadratic; the partner `3bc−a > b`).
  So uniqueness at `c` reduces to **middle-entry uniqueness**.
- **Spine realization** (`MarkovCassiniBridge.spine_residue_farey` + `spine_residue_strict_mono`):
  on the Fibonacci spine the `(residue fib(2n), max fib(2n+1))` pairs are Farey/Stern-Brocot
  neighbors (`fib(2n+1)·fib(2n+2)=fib(2n)·fib(2n+3)+1`), and the residue ratio `u_n/m_n` is
  **strictly increasing** (`fib(2n)·fib(2n+3) < fib(2n+1)·fib(2n+2)`) — Zhang Lemma 2 realized ON
  the spine.

## ★ NEW: `Real213/SternBrocotMarkov` (16 PURE) — the recovery vehicle + expert blueprint
Two deep literature agents (Lang–Tan + Zhang) gave a concrete Mathlib-free plan; the **Markoff-matrix
carrier** is recommended (Frobenius identities = one-multiply entry read-off via `det=1`).  Built:
the **proper det-1 Stern-Brocot tree** (`sbInterval_adj`, `sbInterval_mediant_coprime` — the repo's
`SternBrocotReachable` is all-pairs, not this) AND the **Markoff-matrix tree** (`det2_mul` backbone,
`genL/genR`, `mMat`, `mMat_det1`: every node `det=1`; `markovNum=(M)₂₁`, `markovRes=(M)₂₂−(M)₂₁`;
`markov_root_node`: 1/1↦(5,2)).  Remaining (in G173 "Execution blueprint", dependency order): entry
shape `a+d=3c`; Frobenius identity `u_t m_r − u_r m_t = m_s` via `M_r⁻¹M_t=M_s` (ring_intZ);
`global_mono` (Zhang Lemma 2); window; ⟹ `SamePairInjective` ⟹ `MarkovMaxUnique`.  **Prime-power
uniqueness (Button) needs only these 3–6 steps** (root-count already done).

## Next frontier: `SamePairInjective` for all `c` (= Zhang Lemma 2 / Farey-monotone recovery)
Scoping (Explore agent) + a **strategic correction**: the repo's `Mobius213SternBrocot`
`reachable_of_pos` proves `∀ m k, 1 ≤ m+k → SternBrocotReachable (m,k)` — **every** pair (no
coprimality!).  So `SternBrocotReachable` is the full mediant-closure (all pairs), **NOT** the
injective/unique-path Stern-Brocot tree — it **cannot** be the recovery's injectivity backbone.  A
real recovery needs **canonical continued-fraction paths** built on `farey_mediant_coprime` +
`farey_mediant_adjacent` (now in `MarkovInjectivity` §5), essentially from scratch.  (The naive
"SB-reachable ⟹ coprime" is also false: `(2,2)=(1,0)+(1,2)` is reachable.)  A real bridge needs the *adjacency-restricted* mediant (Farey neighbours, det ±1) or a
direct Farey-order/monotonicity argument.  Layers: (1) **DONE** — Farey-adjacency foundations `farey_mediant_coprime` (`p·s=q·r+1 ⟹
gcd(p+r,q+s)=1`) + `farey_mediant_adjacent` (mediant stays det-1 to both parents); (2) Markov-pair
→ Farey-slope map; (3) **the deep open piece** — residue strictly monotone in slope
(`farey_slope_monotone`, Zhang Lemma 2), realized so far only on the spine (`spine_residue_strict_mono`).
`ConvergentDet.det_one_four_readings` (Farey det=1, the four readings incl. `spine_residue_farey`)
is the anchor.  This is a multi-session project; the spine instances show the shape.
  See G173 "Injectivity analysis".

Full `lake build` clean.  Markov: `MarkovUniqueness` **80 PURE** + `MarkovCassiniBridge` 3 PURE +
`MarkovModularBridge` 2 PURE + `ModArith/MarkovPrimeFactor`
28 PURE = 113, all ∅-axiom.  **★ Frobenius uniqueness verified for EVERY Markov number
`2 ≤ c ≤ 1325`** — `{2,5,13,29,34,89,169,194,233,433,610,985,1325}`, all unconditional ∅-axiom,
each a one-liner via `markov_max_unique_of_{2,4}roots` (or the small `markov_max_unique_{5,13,29,34}`
decides).  **Practical wall**: the in-kernel `decide` over `b<c` stack-overflows for `c ≳ 1500`
(1597, 2897 confirmed) — larger Markov numbers need the general residue-map injectivity, not
enumeration.

## ★ CAPSTONES — UNCONDITIONAL ∅-axiom uniqueness at TWO 4-root composite Markov numbers
`markov_max_unique_1325 : MarkovMaxUnique 1325` (`1325=5²·53`, triple `(13,34,1325)`) **and**
`markov_max_unique_985 : MarkovMaxUnique 985` (`985=5·197`, triple `(2,169,985)`) — both with no
hypotheses, both `#print axioms` clean.  The mod-collapse is now general
(`markov_factor_dvd_sum`: `c=k·p ⟹ p∣a²+b²`); each new composite needs only its root-set lemma,
per-root certs, and per-prime reduced-equation no-solution decides.  Template details below.
The first complete Markov uniqueness theorem at a **4-root composite Markov number**
(`1325 = 5²·53`), with no hypotheses.  The 2-D `∀a∀b` `decide` is infeasible (stack overflow);
the proof is a **2-D→1-D reduction** + **finite descent**:
- `markov_recovery` + `markov_root_recovery`: a triple `(a,b,c)` with `gcd(b,c)=1` maps to a root
  `u=(a·b⁻¹) mod c` of `x²≡−1`, and `a=(u·b) mod c` recovers it.  So a triple is pinned by `(u,b)`.
- `sqrtNegOneRoots_1325`: the root set is exactly `{182,507,818,1143}` (1-D decide).
- `markov_root_{182,1143}` phantom (`∀b ¬`), `markov_root_{507,818}` valid (each closes one) — 1-D.
- `markov_max_unique_of_single` / `..._1325_of_coprime`: assembles the above into `MarkovMaxUnique`
  conditional on coprimality.
- `markov_hcop_1325`: discharges coprimality **unconditionally** — `p∣b ⟹ p∣a` (mod-`p` of the
  equation, `markov_{5,53}_dvd_sum` + `dvd_of_sq_dvd_cert`) ⟹ the `÷25`/`÷53²` generalised Markov
  equation `a²+b²+70225=3975ab` / `+625`, which has **no** bounded solution
  (`reduced_eq_{5,53}_no_sol`).  Pure finite descent — no infinite descent, no tree reachability.

(Earlier in session: main merge + `ring_nat` graft into the Markov polynomial-identity lemmas;
verbose `rw` chains → one-line `ring_nat`, purity preserved.)

## Goal
Marathon research on the **Markov uniqueness conjecture** (Frobenius 1913, classically open):
prove ∅-axiom neighbours, run agent discussion, build conjectures.

## What Was Done This Session

### New module `lean/E213/Lib/Math/Real213/MarkovUniqueness.lean` (44 PURE / 0 dirty)
The ∅-axiom **arithmetic spine** of the conjecture — none of this machinery existed in the repo.

- **§1–2 Neighbor congruence.** `markov_le_3mul` (every entry `≤ 3·`product of other two);
  `markov_neighbor_dvd` — **`c ∣ a²+b²`** with witness `a²+b² = c·(3ab−c)` (the lever of every
  partial result); `markov_neighbor_dvd_all` (3 symmetric), `markov_neighbor_residue` (`%c=0`).
- **§3 The `√(−1)` encoding.** `neg_one_qr_of_inverse` — if `b·b' = 1+c·j` (b invertible mod c)
  then **`c ∣ (a·b')²+1`**, i.e. `−1` is a QR mod `c`, witnessed by `u = a·b'`.  The exact form
  the prime-power theorems (Baragar/Button/Zhang) exploit.  Subtraction-free except one
  `dvd_sub_213`; additive inverse form `b·b'=1+c·j` keeps it clean.
- **§3b Toward coprimality.** `markov_common_dvd_sq` — `d∣b → d∣c → d∣a²` (descent-free, from
  `a²=3abc−(b²+c²)`); `markov_gcd_dvd_sq` — `gcd(b,c)∣a²`.  Foothold for pairwise coprimality.
- **§4 Encoding fires.** `neg_one_qr_mod_{5,29,433}` on triples `(1,2,5),(2,5,29),(5,29,433)`.
- **§5 Computational uniqueness.** `markov_max_unique_{5,13,29,34}` + `markovMaxUnique_{5,13,29}`
  — the conjecture verified decidably at small maxima.  (decide heartbeats out for `c≥169`.)
- **§8 Fibonacci spine via Cassini + recurrence.** `fib_spine_sqrt_neg_one` (`fib(2n+3) ∣
  fib(2n+2)²+1`, ∀n); `fib_spine_recurrence`/`pell_spine_recurrence` — the trace-`NS`(=3)/silver(=6)
  linear recurrences of the Markov spines (C-finite; the Vieta jump; Casoratian = Cassini = √(−1)).
- **§9 Cohn matrix.** `cohn_sq_neg_one_mod` — `C²≡−I mod c` for `tr=3c, det=1` (Cayley–Hamilton),
  pure ℕ: the order-4 generator `S` (Gaussian `i`) survives mod every Markov number.
- **§10 Pairwise coprimality (C2/C3).** `coprime_vieta_step` (Vieta step preserves `gcd`),
  `MarkovReachable` (inductive tree), `markov_reachable_coprime` (every tree triple pairwise
  coprime), `markov_reachable_is_triple` (sound: reachable ⟹ markovEq), `markov_reachable_gcd_bc`
  (the `gcd(b,c)=1` the encoding needs).  No descent / no Hurwitz — preservation + induction.
- **§11 Encoding from a modular inverse.** `neg_one_qr_of_mod`: `(b·b')%c = 1 ⟹ c ∣ (a·b')²+1`
  (residue form, via `AddMod213.div_add_mod`).
- **§6 `p≡3` obstruction.** `no_sqrt_neg_one_mod_{3,7,11,19}` (`−1` non-residue mod `p≡3(4)`)
  + `sqrt_neg_one_mod_5_and_13` contrast.
- **§7 The conjecture, formalised.** `MarkovMaxUnique c`, `SqrtNegOneTwoRoots c` (abbrev so
  `decide` sees it); reduction `SqrtNegOneTwoRoots c → MarkovMaxUnique c` documented as an
  **explicit OPEN target** (not claimed — red-team warned against vacuity).  Prime powers hold
  (`sqrtNegOneTwoRoots_{5,13,25,29}`); `not_sqrtNegOneTwoRoots_65` (c=65=5·13 has 4 roots
  {8,18,47,57}) pinpoints the composite-`c` onset of the open difficulty.

**Purity note**: all `decide` statements use the `%`-residue form (`(x*x+1)%c=0`), NOT `∣` —
the `Decidable (a∣b)` instance leaks `propext`; `Nat.decidableBallLT`+`%`+`decEq` are pure.

### Agents (the "discussion")
4 research agents: literature survey (Frobenius/Baragar/Button/Zhang/Aigner; Rabideau-Schiffler
& Lagisquet et al. for the now-proven monotonicity conjectures), repo-infra survey (found
`Gcd213.{dvd_sub_213,dvd_add_213}`, `AddMod213.*`, `ModBezout.modBezout`), and an adversarial
red-team (triviality/vacuity check on the encoding, graded conjecture slate, devil's-advocate +
rebuttal).  Synthesis recorded in `research-notes/G173`.

### Docs
- `research-notes/G173_markov_uniqueness.md` — conjecture slate C1–C8 (graded ∅-axiom
  tractability), literature, red-team discussion, 213-native angle.
- `research-notes/G174_markov_newton_synthesis.md` — **idea-level graft of merged `main`**: Markov
  spine = C-finite trace-`NS` recurrence (Newton/holonomicity layer); `√(−1)` residue = Casoratian
  (Cassini); uniqueness = Myhill–Nerode minimality of the tree coalgebra (StateMachine), localising
  the open C6 crux to "insufficient observable at composite `c`".
- `theory/math/analysis/markov_uniqueness.md` — promoted chapter mirroring the Lean.
- Wired into `theory/math/INDEX.md` + cross-link from `markov_spectrum.md`.
- `Real213.lean` umbrella imports `MarkovUniqueness`.

## Current Precision Results (0 free parameters)
**No physics constants changed** (pure math: Diophantine / number theory).  Precision table
unchanged — see `catalogs/physics-constants.md`, `catalogs/falsifiers.md`.

## Open Problems (Priority Order)

### 1. C2/C3 — pairwise coprimality — DONE along the tree (§10)
`markov_reachable_coprime` (every reachable triple pairwise coprime, via `coprime_vieta_step`
preservation + induction over `MarkovReachable`); `markov_reachable_gcd_bc` gives `gcd(b,c)=1`.
No descent / no Hurwitz needed.  **C2→C4 bridge now DONE** (`MarkovPrimeFactor.inverse_of_coprime`
via `xgcdAux_dvd_both`, the xgcd gcd-component divides both inputs under `fuel≥r₁+1`):
`markov_reachable_neg_one_qr` fires the encoding unconditionally on every reachable triple
(`1<c`).  (Gap to *all* Markov triples = "every triple reachable" = Markov's theorem, the
descent — separate.)

### 2. C5 `p≡3` no-root, GENERAL — DONE (`ModArith/MarkovPrimeFactor`, 16 PURE)
`no_sqrt_neg_one_4k3`: for `p=4k+3` with the prime-gcd hypothesis, `¬(p∣x²+1)`, via
`universal_flt_main` (`x^(p−1)=(x²)^(2k+1)≡(−1)^(2k+1)≡−1` vs Fermat `≡1`).  Helpers
`neg_one_sq_mod`, `neg_one_odd_pow_mod`, `pred_mod_of_dvd_succ`.  Concrete `no_sqrt_neg_one_mod_{7,11}`.
**Remaining C5**: the `p≡1(mod4)` *existence* branch (root of `x²≡−1 mod pᵏ`) — hard without
`Classical` (Wilson construction).

### 3b. C7 at 1325 AND 985 — DONE UNCONDITIONALLY (capstones, see top).
`markov_max_unique_{1325,985}` close uniqueness at two 4-root composite Markov numbers, no
hypotheses, ∅-axiom.  The route (recovery reduction + finite-descent coprimality) is **reusable**:
next is `610 = 2·5·61` (NOTE: even — factor 2 needs the mod-2 parity branch `2∣b ⟹ 2∣a`, and the
`÷4` reduced eq `a²+b²+93025=1830ab` over `305²` — heavier).  Recipe per composite `c`:
`sqrtNegOneRoots_<c>` (1-D), per-root phantom/valid 1-D certs, `markov_no_top_<c>`,
`reduced_eq_<p>_<c>_no_sol` for each prime `p∣c` (`÷p²`, bound `c/p`), `not_<p>_dvd_b_<c>` (reuse
`markov_factor_dvd_sum` + `dvd_of_sq_dvd_cert`), `div<c>_trivial_of_...`, `markov_hcop_<c>`.
**Cost warning**: the largest `reduced_eq` decide (266² for 1325, 198² for 985) needs
`maxHeartbeats 0` + `maxRecDepth 20000`, ~60–110 s.  And the `dvd_of_sq_dvd_cert` residue cert
`∀r<p, r²≡0→r=0` needs `maxRecDepth ≥ ~4000` once `p` is large (e.g. 197).

### 3c. Markov descent theorem — DONE (§10b).  General coprimality achieved.
`markov_ordered_reachable`: every ordered Markov triple is reachable from `(1,1,1)`
(`reachable_of_fuel`, structural recursion on a fuel bounding the max — ∅-axiom, no
`WellFounded.fix`; `c≥2` descends to `{a,b,3ab−c}`, max `= b < c`, via the §2b engine).
`markov_ordered_coprime`: pairwise coprime for ALL triples (descent ∘ `markov_reachable_coprime`).
`markov_hcop_general (c≥2)`: the `hcop` input for ALL `c` at once — `markov_max_unique_{1325,985}`
now route through it; the per-c reduced-equation method (266²/198² decides) is deleted.

### 3d. Per-c uniqueness PACKAGED + COMPLETE to 1325.
`markov_max_unique_of_{2,4}roots c a₀ b₀ <roots> (by decide)×(4|6)` closes any prime/prime-power
(2-root) or composite (4-root) Markov number in one line (root-set disjunction + per-root certs;
coprimality/`a≥1`/`b<c` discharged internally).  All Markov numbers `2 ≤ c ≤ 1325` are now done.
**The `decide` wall is `c≈1325`** (1597/2897 stack-overflow even at `maxRecDepth 60000` — it's a
native C-stack overflow in kernel whnf of the `decidableBallLT` term, NOT a `maxRecDepth` limit, so
unfixable by raising it).  Going higher (or to the infinite families) requires the general
residue-map injectivity, below.  (An 8-root analogue would handle `c` with 3 distinct odd primes,
but the smallest such Markov number is far past the `decide` wall.)

### 3e. GENERAL conjecture crux (still open).
The residue-map injectivity (`triple ↦ a·b⁻¹ mod c` is injective on triples with max `c`) for
arbitrary `c` is the remaining open part — per-c certs sidestep it by enumerating the finite root
set.  The coprimality half is fully general (`markov_ordered_coprime`).  A genuine general-`c`
result would need to bound the number of ordered triples per root *without* enumeration — the
`SqrtNegOneTwoRoots → MarkovMaxUnique` reduction at prime powers (Button/Zhang) is the model;
formalising that family (`MarkovMaxUnique (p^k)`) is the next non-mechanical target.

### 3. C6 — root-count reduction `SqrtNegOneTwoRoots c → MarkovMaxUnique c` — classically OPEN-ish
**Input now done for prime POWERS** (full Button/Zhang class): `two_roots_of_prime` (primes) and
`two_roots_of_prime_pow` (`SqrtNegOneTwoRoots (p^(k+1))`, odd prime `p`) — `p` divides ≤1 of
`x±y`, the coprime one cancels via `euclid_of_coprime` + `coprime_prime_pow`.  So the reduction's
hypothesis is discharged at every prime-power maximum; closing the residue-map injectivity (below)
would give prime-power-Markov uniqueness (C7).
The *implication* is classical; the crux is **injectivity of the residue map**
`triple ↦ a·b⁻¹ (mod c)`.  Keep as a single named open Lean target; attempt only the
injectivity lemma in isolation, guarding against vacuity.  Do NOT claim the full reduction.

### 4. C7 — prime-power Markov numbers unique (Baragar/Button/Zhang) = C5∘C6.  Aspirational capstone.

## 213-native conjecture (to sharpen)
The `√(−1)`-residue indexing a Markov number = the order-4 elliptic generator `S` (Gaussian `i`)
of `PSL(2,ℤ)=ℤ₂*ℤ₃` (`ModularElliptic`).  Conjecture: the Markov↦`√(−1)`-residue map is the
Stern-Brocot↦`PSL(2,ℤ)`-elliptic correspondence on the `c=2` `K_{3,2}` axis.

## Dead ends (don't repeat)
- `decide` on `c ∣ …` → `propext` DIRTY.  Use `% c = 0`.
- `markov_composite_separation` (c=1325) uses `decide` over `∀ b<1325` (×2) — `maxRecDepth
  40000`, ~60s to build that module.  Larger composites cost more; 1D recovery search only.
- `reduced_eq_5_no_sol` (`∀a<266 ∀b<266`) needs `maxHeartbeats 0` + `maxRecDepth 20000`, ~110s.
  The 2-D `∀a∀b markovEq` decide at c=1325 STACK-OVERFLOWS (don't attempt) — must go 1-D.
- `decide` on `MarkovMaxUnique`/uniqueness for `c≥169` → heartbeat timeout (>200000) /
  max-recursion.  Cap in-kernel `decide` at `c≈34`; cite external enumeration for larger.
- `set` tactic = Mathlib, unavailable.  Use `obtain ⟨M,_⟩ : ∃ M, …`.
- A docstring may NOT be followed by `set_option … in` (parser rejects); order
  `set_option … in` *before* the docstring.
- `def` for a decidable Prop-shape hides the `Decidable` instance from `decide`; use `abbrev`,
  and put each bound `x < c` *immediately* after its binder (interleaved `∀ x y, x<c→y<c` breaks
  `Nat.decidableBallLT`).

## File Map
```
NEW Lean (∅-axiom):
  lean/E213/Lib/Math/Real213/MarkovUniqueness.lean       ← neighbor congruence + √(−1) encoding + coprimality (43 PURE)
  lean/E213/Lib/Math/ModArith/MarkovPrimeFactor.lean     ← p≡3 no-root (FLT), xgcd-correctness inverse, general Euclid, ≤2 roots mod p^(k+1) Button/Zhang (28 PURE)
NEW theory chapter:
  theory/math/analysis/markov_uniqueness.md
NEW research note:
  research-notes/G173_markov_uniqueness.md               ← conjecture slate C1–C8 + red-team
MODIFIED:
  lean/E213/Lib/Math/Real213.lean, ModArith.lean         ← umbrella imports
  theory/math/INDEX.md, theory/math/analysis/markov_spectrum.md  ← index + cross-link
```
