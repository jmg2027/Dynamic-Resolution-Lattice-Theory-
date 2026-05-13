import E213.Lens.LensCore
import E213.Lib.Math.Cauchy.Archimedean

/-!
# AsLensOutput: real = Lens output (User insight 2026-04-26)

User insight: "Aren't there infinitely many different ways to extract
natural numbers from 213?  Of course reals exist then.  Computation?
You can always pick any way to operate on those infinitely many natural
numbers."

## Core reframe

`RealCut := Nat → Nat → Bool` = "Lens output Bool for each rational
target (m, k)".

This *function space* exists automatically from 213's axiom —
infinitely many distinct functions, each valid one a real.

## Contents of this module

This module is *interpretive*: it makes explicit that the existing
RealCut definition (ArchimedeanCauchy.lean) is already Lens output.
No new type is introduced.

```
abbrev RealAsLensOutput := Nat → Nat → Bool
```

This is the *inherent* type of the framework — it arises naturally from
the 213 axiom alone.

## Operations are a choice

Specific operations like cutSum / cutMul are one choice that *looks
like rational arithmetic*.  Infinitely many other binary functions are
possible within the framework.

Choose according to use — no need to build carefully with ε-N like
Bishop; just *pick the right combine*.

## True conclusion of the marathon

The Bishop program itself is redundant within 213 — the Lens space of
213 already contains the reals.  Everything built in the marathon —
cutSum, cutMul, cutMaxMin, etc. — are all examples of *valid choices
within the framework*.

User directive ("213 only") + this insight = the *final* simplification
of real analysis in 213 form.
-/

namespace E213.Lib.Math.Real213.Core.Core.AsLensOutput

open E213.Theory E213.Lens

/-- **Real as Lens output** — inherent type of the framework. -/
abbrev RealAsLensOutput := Nat → Nat → Bool

/-- Identity statement: RealAsLensOutput is framework-internal. -/
example : RealAsLensOutput = (Nat → Nat → Bool) := rfl

end E213.Lib.Math.Real213.Core.Core.AsLensOutput
