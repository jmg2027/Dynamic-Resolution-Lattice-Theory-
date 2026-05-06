/-!
# Lens.Instances.EndpointBehavior — endpoint-behavior lens

The pattern formalised by `Passthrough_at` (parts 7+8 of the funext
refactor).  A higher-order function `f : (Nat → Nat → Bool) → (Nat
→ Nat → Bool)` is viewed only through its **behavior at the
endpoints** `(constCut 0 1)` and `(constCut 1 1)` — collapsing all
internal behavior into a single endpoint-pair.

Concrete realisation:

  - `Passthrough f := { left : f 0 = 0, right : f 1 = 1 }` (function-eq)
  - `Passthrough_at f := { left : ∀ m k, f 0 m k = 0 m k,
                            right : ∀ m k, f 1 m k = 1 m k }`
    (pointwise — PURE)
  - The lens kernel: `f ~ g` iff `f` and `g` share endpoint
    behavior pointwise.

This lens enables the entire MVT/FTC at unit bracket arc to be
strict ∅-axiom: any `f` that "passes through" (0,0) and (1,1)
yields the same flux as the identity function on those endpoints.
-/

namespace E213.Lens.Instances.EndpointBehavior

/-- A function's endpoint behavior (constCut 0 1 ↦ a, constCut 1 1 ↦ b)
    expressed as a Bool pair at any query point (m, k).  Pointwise
    extraction — does NOT collapse function eq. -/
def project_at (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (zero : Nat → Nat → Bool) (one : Nat → Nat → Bool) (m k : Nat) :
    Bool × Bool :=
  (f zero m k, f one m k)

/-- Two functions agree at endpoints if their pointwise projection
    matches at every query point. -/
def endpointEq (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (zero one : Nat → Nat → Bool) : Prop :=
  ∀ m k, project_at f zero one m k = project_at g zero one m k

end E213.Lens.Instances.EndpointBehavior
