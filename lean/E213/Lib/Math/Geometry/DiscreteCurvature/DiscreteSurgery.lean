import E213.Meta.Int213
import E213.Meta.Int213.Bound
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Combinatorics.IntGridSum
import E213.Lib.Math.Foundations.MonovariantFlow

/-!
# Discrete surgery — classification, curvature ledger, and finite termination (∅-axiom)

**κ-solution / surgery classification** — the flow develops necks, one must classify the
states, cut and cap, and bound the number of surgeries.  This file establishes the discrete
core of that on the graph (1-complex) category, where curvature ↔ topology is already a
theorem (`DiscreteGaussBonnet`), all `∅`-axiom:

  * **General Gauss–Bonnet** (`gauss_bonnet_general`): for *any* finite graph given its
    degree field and the handshake identity `Σ deg = 2E`, the total vertex curvature is
    `Σ_v (2 − deg v) = 2·χ`, `χ = V − E` — the bookkeeping law every surgery respects
    (generalizes the `K_{m,n}`-specific `gauss_bonnet_Kmn`).
  * **The surgery step**: cut one *neck* edge — an edge lying on a cycle (`b₁ ≥ 1`), so
    the complex stays connected: `E ↦ E − 1`, `V` fixed.  Ledger: `χ` rises by exactly
    `1` (`surgery_euler`), total curvature by exactly `+2` (`surgery_curvature`) — each
    surgery is a quantum of positivity, the cut-and-cap of the cigar/neck.
  * **Classification dichotomy** (`surgery_dichotomy`): a connected state is either
    **round** — `b₁ = 0`, a tree, total curvature `+2 > 0`, *terminal*, no neck exists —
    or **neck-bearing** — `b₁ ≥ 1`, total curvature `≤ 0`, surgery applies.  The discrete
    κ-solution classification shape: every state is round or admits a neck to cut.
  * **Finite termination, exact count** (`surgery_terminates`, `surgery_count`): `b₁` is
    the monovariant — each surgery drops it by exactly `1`, so the flow terminates
    after **exactly `b₁` surgeries** at the round state (via the FLOW archetype
    `flow_reaches`).  The discrete "finitely many surgeries, then extinction".

Worked instance: `K_{3,2}` (`V = 5`, `E = 6`, `b₁ = 2`) needs exactly `2` surgeries;
its curvature ledger runs `−2 → 0 → +2` (`k32_surgery`).

**Honest boundary**: this is the surgery *ledger* — Euler/curvature bookkeeping, the
round-or-neck dichotomy, and the termination bound — in the graph category.  The
smooth κ-solution classification (shrinking solitons, Bryant), the neck-detection
*geometry* (canonical neighbourhoods), and **no-local-collapsing compactness** are not
treated here.
-/

namespace E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteSurgery

open E213.Meta.Int213
open E213.Lib.Math.Combinatorics.IntGridSum (gridSumZ gridSumZ_sub gridSumZ_const)
open E213.Lib.Math.Foundations.MonovariantFlow (flow_reaches IsNormalForm iter)

/-! ## §1 — general discrete Gauss–Bonnet (the ledger's conservation law) -/

/-- Euler characteristic of a `(V, E)` graph ledger: `χ = V − E`, over `ℤ`. -/
def eulerVE (V E : Nat) : Int := (V : Int) - (E : Int)

/-- ★★★★ **General discrete Gauss–Bonnet**: for any finite graph — degree field
    `deg : Nat → Nat` on `V` vertices with the handshake identity `Σ_v deg v = 2E` —
    the total vertex curvature `Σ_v (2 − deg v)` equals `2·χ`.  Generalizes
    `gauss_bonnet_Kmn` from the complete-bipartite family to every graph: the surgery
    ledger's conservation law. -/
theorem gauss_bonnet_general (V E : Nat) (deg : Nat → Nat)
    (hhs : gridSumZ V (fun v => (deg v : Int)) = 2 * (E : Int)) :
    gridSumZ V (fun v => 2 - (deg v : Int)) = 2 * eulerVE V E := by
  rw [gridSumZ_sub V (fun _ => (2 : Int)) (fun v => (deg v : Int)),
      gridSumZ_const V 2, hhs]
  unfold eulerVE
  ring_intZ

/-! ## §2 — the surgery step: cut a neck edge (`E + 1 ↦ E`, connectivity kept) -/

/-- ★★★ **Surgery raises `χ` by exactly 1**: cutting one neck edge (`E + 1 ↦ E` edges,
    vertices fixed) is a unit step of the Euler characteristic. -/
theorem surgery_euler (V E : Nat) : eulerVE V E = eulerVE V (E + 1) + 1 := by
  unfold eulerVE
  have hcast : ((E + 1 : Nat) : Int) = (E : Int) + 1 := Int.ofNat_add E 1
  rw [hcast]
  ring_intZ

/-- ★★★★ **Surgery raises total curvature by exactly `+2`** (via Gauss–Bonnet
    `Σκ = 2χ`): each cut-and-cap injects one quantum `+2` of positivity — the discrete
    form of surgery replacing a neck by positively-curved caps. -/
theorem surgery_curvature (V E : Nat) :
    2 * eulerVE V E = 2 * eulerVE V (E + 1) + 2 := by
  rw [surgery_euler V E]
  ring_intZ

/-- For a connected graph on `m + 1` vertices with `b₁ = b` (so `E = m + b` edges:
    `m` tree edges + `b` cycle edges): `χ = 1 − b₁` — Euler ↔ Betti. -/
theorem euler_eq_one_sub_b1 (m b : Nat) :
    eulerVE (m + 1) (m + b) = 1 - (b : Int) := by
  unfold eulerVE
  have h1 : ((m + 1 : Nat) : Int) = (m : Int) + 1 := Int.ofNat_add m 1
  have h2 : ((m + b : Nat) : Int) = (m : Int) + (b : Int) := Int.ofNat_add m b
  rw [h1, h2]
  ring_intZ

/-- **Total curvature `= 2 − 2·b₁`** (connected): positive exactly at `b₁ = 0`. -/
theorem totalCurv_b1 (m b : Nat) :
    2 * eulerVE (m + 1) (m + b) = 2 - 2 * (b : Int) := by
  rw [euler_eq_one_sub_b1]
  ring_intZ

/-! ## §3 — classification: round or neck-bearing -/

/-- ★★★★★ **The surgery classification dichotomy** (discrete κ-solution shape): a
    connected state is either **round** — `b₁ = 0`, total curvature `+2 > 0`, terminal
    (a tree has no cycle edge to cut) — or **neck-bearing** — `b₁ ≥ 1`, total curvature
    `≤ 0`, and a neck exists, so surgery applies.  Every state is round or admits
    surgery; there is no third class. -/
theorem surgery_dichotomy (m b : Nat) :
    (b = 0 ∧ 2 * eulerVE (m + 1) (m + b) = 2)
    ∨ (1 ≤ b ∧ 2 * eulerVE (m + 1) (m + b) ≤ 0) := by
  cases b with
  | zero =>
    left
    refine ⟨rfl, ?_⟩
    rw [totalCurv_b1]
    decide
  | succ b' =>
    right
    refine ⟨Nat.succ_le_succ (Nat.zero_le b'), ?_⟩
    rw [totalCurv_b1]
    have hcast : (1 : Int) ≤ ((b' + 1 : Nat) : Int) :=
      Order.ofNat_le (Nat.succ_le_succ (Nat.zero_le b'))
    have h2 : (2 : Int) * 1 ≤ 2 * ((b' + 1 : Nat) : Int) :=
      OrderMul.mul_le_mul_left_nonneg hcast 2 (by decide)
    rw [mul_one] at h2
    apply Order.le_of_sub_nonneg
    rw [show (0 : Int) - (2 - 2 * ((b' + 1 : Nat) : Int))
          = 2 * ((b' + 1 : Nat) : Int) - 2 from by ring_intZ]
    exact Order.sub_nonneg_of_le h2

/-! ## §4 — termination: exactly `b₁` surgeries, then the round state -/

/-- The surgery flow on the `b₁` ledger: cut one neck while one exists (`b ↦ b − 1`;
    the round state `b = 0` is fixed). -/
def surgeryFlow (b : Nat) : Nat := b - 1

/-- Per-step descent: surgery strictly drops `b₁`, or the state is already round. -/
theorem surgeryFlow_descent (b : Nat) : surgeryFlow b < b ∨ surgeryFlow b = b := by
  cases b with
  | zero => right; rfl
  | succ b' => left; exact Nat.lt_succ_self b'

/-- ★★★★ **Surgery terminates** (via the FLOW archetype): from any initial `b₁` the
    surgery flow reaches a normal form — the surgery count is finite, no infinite surgery
    cascade (Perelman's finitely-many-surgeries, in the discrete ledger). -/
theorem surgery_terminates (b : Nat) :
    ∃ n, IsNormalForm surgeryFlow (iter surgeryFlow n b) :=
  flow_reaches surgeryFlow (fun b => b) surgeryFlow_descent b

/-- A surgery fixed point is exactly the round state: `surgeryFlow b = b ⟹ b = 0`. -/
theorem surgeryFlow_fixed_round (b : Nat) (h : surgeryFlow b = b) : b = 0 := by
  cases b with
  | zero => rfl
  | succ b' => exact absurd h (Nat.ne_of_lt (Nat.lt_succ_self b'))

/-- Pure `b − 1 − n = b − (n+1)` (core `Nat.sub_sub` carries `propext`); the inductive
    step is definitional (`Nat.sub` recursion is `pred`-iteration). -/
private theorem sub_one_sub : ∀ (b n : Nat), b - 1 - n = b - (n + 1)
  | _, 0 => rfl
  | b, n + 1 => congrArg Nat.pred (sub_one_sub b n)

/-- The flow after `n` surgeries: `b₁ − n` (truncated). -/
theorem iter_surgery : ∀ (n b : Nat), iter surgeryFlow n b = b - n
  | 0, b => rfl
  | n + 1, b => by
    show iter surgeryFlow n (b - 1) = b - (n + 1)
    rw [iter_surgery n (b - 1)]
    exact sub_one_sub b n

/-- ★★★★★ **Exactly `b₁` surgeries**: starting from first Betti number `b`, after
    precisely `b` surgery steps the state is round (`b₁ = 0`) — the surgery count is not
    just finite but *equal to the topology's cycle count*, and the terminal state has
    total curvature `+2` (`surgery_dichotomy`): finite extinction at the round cap. -/
theorem surgery_count (b : Nat) : iter surgeryFlow b b = 0 := by
  rw [iter_surgery b b]
  exact Nat.sub_self b

/-- ★★★★★ **The discrete surgery package**: dichotomy (round XOR neck-bearing) +
    termination + exact count, one bundle — the discrete core of κ-solution /
    surgery classification. -/
theorem surgery_classification (m b : Nat) :
    ((b = 0 ∧ 2 * eulerVE (m + 1) (m + b) = 2)
      ∨ (1 ≤ b ∧ 2 * eulerVE (m + 1) (m + b) ≤ 0))
    ∧ iter surgeryFlow b b = 0
    ∧ (∀ b', surgeryFlow b' = b' → b' = 0) :=
  ⟨surgery_dichotomy m b, surgery_count b, surgeryFlow_fixed_round⟩

/-! ## §5 — worked instance: `K_{3,2}` needs exactly two surgeries -/

/-- ★★★ **`K_{3,2}` surgery ledger**: the complete bipartite graph `K_{3,2}` (`V = 5`,
    `E = 6`, `b₁ = 2`) starts at total curvature `−2`, needs exactly `2` surgeries, and its
    ledger runs `−2 → 0 → +2` (each cut `+2`), ending round. -/
theorem k32_surgery :
    2 * eulerVE 5 6 = -2
    ∧ 2 * eulerVE 5 5 = 0
    ∧ 2 * eulerVE 5 4 = 2
    ∧ iter surgeryFlow 2 2 = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩


/-! ## §3 — 3-regular (non-bipartite) Gauss–Bonnet instances -/

/-- ★ **Discrete Gauss–Bonnet for `K₄`** (complete graph, 3-regular, non-bipartite):
    `Σ_v (2 − deg v) = 4·(−1) = −4 = 2·(V − E) = 2·(4 − 6)`.  The handshake `Σ deg = 12 = 2·6`
    discharges `gauss_bonnet_general` — the conservation law holds beyond the bipartite `K_{m,n}`. -/
theorem gauss_bonnet_K4 :
    gridSumZ 4 (fun _ => 2 - ((3 : Nat) : Int)) = 2 * eulerVE 4 6 :=
  gauss_bonnet_general 4 6 (fun _ => 3) (by decide)

/-- ★ **Discrete Gauss–Bonnet for the cube graph `Q₃`** (3-regular, 8 vertices, 12 edges):
    `Σ_v (2 − 3) = 8·(−1) = −8 = 2·(8 − 12)`.  Handshake `Σ deg = 24 = 2·12`. -/
theorem gauss_bonnet_cube :
    gridSumZ 8 (fun _ => 2 - ((3 : Nat) : Int)) = 2 * eulerVE 8 12 :=
  gauss_bonnet_general 8 12 (fun _ => 3) (by decide)

/-- ★ **Gauss–Bonnet for the Petersen graph** (3-regular, non-bipartite, `V=10`, `E=15`):
    `Σ_v (2 − 3) = 10·(−1) = −10 = 2·(10 − 15)`.  Handshake `Σ deg = 30 = 2·15`. -/
theorem gauss_bonnet_petersen :
    gridSumZ 10 (fun _ => 2 - ((3 : Nat) : Int)) = 2 * eulerVE 10 15 :=
  gauss_bonnet_general 10 15 (fun _ => 3) (by decide)

/-- ★ **Gauss–Bonnet for the complete graph `K₅`** (4-regular, `V=5`, `E=10`):
    `Σ_v (2 − 4) = 5·(−2) = −10 = 2·(5 − 10)`.  Handshake `Σ deg = 20 = 2·10`. -/
theorem gauss_bonnet_K5 :
    gridSumZ 5 (fun _ => 2 - ((4 : Nat) : Int)) = 2 * eulerVE 5 10 :=
  gauss_bonnet_general 5 10 (fun _ => 4) (by decide)
end E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteSurgery
