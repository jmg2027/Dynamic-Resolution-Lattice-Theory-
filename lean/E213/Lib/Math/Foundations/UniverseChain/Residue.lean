import E213.Theory.Raw.API

/-!
# Step 0 — Residue of distinction = recursion (∅-axiom)

Mingu's articulation:
> "구분을 하면 항상 잔여물이 남는거 아냐?"

Direct reading of `research-notes/G29_residue.md` point 3:
> "그 짝도 다시 가리킬 수 있다."

## Formalization

Recursion is **not** a separate Lens layer — it is the type
signature of `Raw.slash`:

```
slash : (x y : Raw) → (h : x ≠ y) → Raw
                                    ↑↑↑
                              residue inhabits Raw,
                              so it can re-enter as input.
```

The four G29 points map to Raw's constructor + its hypotheses:

| G29 point                            | Raw / slash form               |
|--------------------------------------|--------------------------------|
| 1. 두 가지가 서로 다르게 나타난다     | `Raw.a`, `Raw.b`, `a ≠ b`      |
| 2. 이 둘을 짝지을 수 있다             | `Raw.slash _ _ _` constructor  |
| 3. 그 짝도 다시 가리킬 수 있다        | `slash`'s codomain = `Raw`     |
| 4. 자기 자신과는 짝지을 수 없다        | `(h : x ≠ y)` precondition     |

Step 0 of the deductive chain — *prior to* Atomicity.  All
subsequent steps (atomicity → 5, recursion to d², configCount)
ride on this structural recursion.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.Residue

open E213.Theory

/-- ** point 1**: two distinct primitives. -/
theorem distinct_primitives : Raw.a ≠ Raw.b := by decide

/-- ** point 4**: no self-distinction. -/
theorem no_self_distinction (x : Raw) : ¬ (x ≠ x) := fun h => h rfl

/-- **Depth-1 residue**: pair of two atoms. -/
def d1 : Raw := Raw.slash Raw.a Raw.b distinct_primitives

theorem d1_ne_a : d1 ≠ Raw.a := by decide
theorem d1_ne_b : d1 ≠ Raw.b := by decide

/-- **Depth-2 residue**: residue d1 paired with atom a — the
    residue feeds back into `slash` because its type is `Raw`. -/
def d2 : Raw := Raw.slash d1 Raw.a d1_ne_a

theorem d2_ne_d1 : d2 ≠ d1 := by decide

/-- **Depth-3 residue**: another iteration. -/
def d3 : Raw := Raw.slash d2 Raw.b (by decide)

theorem d3_ne_d2 : d3 ≠ d2 := by decide

/-- ★★★ **Residue recursion witness.**  The `slash` constructor's
    output type `Raw` automatically generates an unbounded chain
    of inhabitants — recursion is structural, not a Lens choice. -/
theorem residue_recursion_witness :
    Raw.a ≠ Raw.b ∧ d1 ≠ Raw.a ∧ d2 ≠ d1 ∧ d3 ≠ d2 :=
  ⟨distinct_primitives, d1_ne_a, d2_ne_d1, d3_ne_d2⟩

end E213.Lib.Math.Foundations.UniverseChain.Residue
