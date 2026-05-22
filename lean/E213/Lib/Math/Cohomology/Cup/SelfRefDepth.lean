import E213.Lib.Math.Cohomology.Cup.LeibnizCatalog

/-!
# Cohomology.Cup.SelfRefDepth — face-iteration depth signature

The twisted Leibniz of the lex-projection cup `(α ⌣ β)` has
correction term `(α ⌣ β)(τ \ {τ[k]})` — the cup itself at the
**middle-removed face**.  Iterating that face-removal traces a
path through the face poset, recording the cup value at each
step:

  step 0: cupList k l α β τ                   (τ of length L)
  step 1: cupList k l α β (τ.eraseIdx k)      (length L-1)
  step 2: cupList k l α β ((τ.eraseIdx k).eraseIdx k)
  ...
  step d: cupList k l α β (... d iterations ...)

The output is a `List Bool` of length `depth` — the
**face-iteration depth signature** of the (α, β, τ) triple at
split position k, parametrised by a fuel-bounded depth.

Physics motivation: at d = 5 (the DRLT count-Lens dimension),
depth-(d-1) = depth-4 signatures probe the `α^(d-1)` suppression
structure observed across DRLT physical constants.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.SelfRefDepth

open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel (cupList)

/-- ★ **Face-iteration depth signature** — recursion on depth fuel.
    At depth 0 returns `[]`.  At depth `d+1` records the current cup
    value, then recurses on the k-erased face at depth `d`.  Output
    length always equals input depth.  PURE. -/
def selfRefIter (k l : Nat) (α β : List Nat → Bool) :
    Nat → List Nat → List Bool
  | 0, _ => []
  | depth + 1, τ =>
    cupList k l α β τ :: selfRefIter k l α β depth (τ.eraseIdx k)

/-- ★ **Length of the depth signature equals the fuel.**  PURE. -/
theorem selfRefIter_length (k l : Nat) (α β : List Nat → Bool) :
    ∀ (depth : Nat) (τ : List Nat),
      (selfRefIter k l α β depth τ).length = depth := by
  intro depth
  induction depth with
  | zero => intro _; rfl
  | succ d ih =>
    intro τ
    show (selfRefIter k l α β d (τ.eraseIdx k)).length + 1 = d + 1
    rw [ih]

/-! ## §2.  d = 5 prototype — DRLT alignment -/

/-- The depth-(d-1) = depth-4 signature on the full Δ⁴ vertex set
    `[0, 1, 2, 3, 4]` at bidegree (1, 1).  For DRLT, d = 5 is the
    count-Lens dimension; depth = d-1 = 4 matches the `α^(d-1)`
    empirical suppression order. -/
def depth4Sig (α β : List Nat → Bool) : List Bool :=
  selfRefIter 1 1 α β 4 [0, 1, 2, 3, 4]

/-- Smoke: `depth4Sig` length is 4.  PURE. -/
theorem depth4Sig_length (α β : List Nat → Bool) :
    (depth4Sig α β).length = 4 :=
  selfRefIter_length 1 1 α β 4 [0, 1, 2, 3, 4]

/-! ## §3.  Concrete signatures (decide-verified) -/

/-- Indicator cochain at single-vertex `i`.  PURE. -/
def α_e (i : Nat) : List Nat → Bool := fun s => decide (s = [i])

/-- Saturated cochain — maps every list to `true`. -/
def all_true_list : List Nat → Bool := fun _ => true

/-- ★ **All-ones depth-4 signature** — maximum saturation.  Every
    cupList value is `true && true = true`.  PURE. -/
theorem depth4Sig_all_true :
    depth4Sig all_true_list all_true_list
    = [true, true, true, true] := by decide

/-! ## §4.  Self-reference saturation count — channel-counting probe

For a single (α, β) pair on Δ⁴ with split position 1, the depth-4
signature is a 4-bit Bool vector.  There are `2^4 = 16` possible
signatures.  Across the indicator-basis pairs `(α_e i, α_e j)` for
`i, j ∈ {0..4}`, the signature distribution probes the
**self-reference depth structure** of the basis. -/

/-- ★ **Depth-4 signature of `(α_e i, α_e j)`** — basis pair
    indicator cochains.  PURE. -/
def basisDepth4Sig (i j : Nat) : List Bool :=
  depth4Sig (α_e i) (α_e j)

/-- For all basis pairs `(α_e i, α_e j)` with i, j ∈ {0..4}, the
    depth-4 signature evaluates concretely.  Spot checks below
    enumerate the structure.  PURE. -/
theorem basisDepth4Sig_0_1 :
    basisDepth4Sig 0 1 = [false, false, false, false] := by decide

/-- ★★★ **The (0, 4) basis pair survives all four iterations**.
    Iteration trace:
      τ_3 = [0, 4]  → α_e 0([0]) ∧ α_e 4([4]) = true ∧ true = true.
    All earlier steps drop a vertex via eraseIdx 1 — the drop-side
    is multi-vertex, so α_e 4 evaluates false until the depth-3
    face shrinks to `[0, 4]` with single-vertex drop-side.  PURE. -/
theorem basisDepth4Sig_0_4 :
    basisDepth4Sig 0 4 = [false, false, false, true] := by decide

theorem basisDepth4Sig_1_2 :
    basisDepth4Sig 1 2 = [false, false, false, false] := by decide

/-- ★★★★ **Sole non-zero basis pair at depth-4 saturation**: across
    all 25 indicator basis pairs `(α_e i, α_e j)` for `i, j ∈ {0..4}`
    on the depth-4 face-iteration signature at split position 1, the
    pair `(0, 4)` is the **unique** pair with a non-zero signature
    bit, and that bit is the last (depth-3) entry.

    Concretely:
      basisDepth4Sig 0 4 = [false, false, false, true]
      basisDepth4Sig i j = [false, false, false, false]   for (i, j) ≠ (0, 4)

    Structural interpretation: of the `5×5 = 25` indicator basis
    pairs at d = 5, exactly **one** survives all four iterations
    of the middle-erase to fire the cup value.  This single
    surviving pair `(0, 4)` is the **boundary-endpoint pair** of
    Δ⁴ — minimum-and-maximum-vertex indicator.  The Lens-output
    count `1 / 25` is the depth-4 saturation density of the
    indicator basis at d = 5.

    PURE (decide-verified). -/
theorem basisDepth4Sig_unique_survivor :
    ∀ (i j : Fin 5),
      basisDepth4Sig i.val j.val
      = if i.val = 0 ∧ j.val = 4
        then [false, false, false, true]
        else [false, false, false, false] :=
  by decide

end E213.Lib.Math.Cohomology.Cup.SelfRefDepth
