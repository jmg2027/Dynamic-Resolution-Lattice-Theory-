import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace
import E213.Meta.Int213.PolyIntMTactic

/-!
# `Mat2` multiplication is associative — the monoid law under the dial

The order-2 dial reads matrices statically (`tr`, `det`, `disc`) and the Cayley–Hamilton identity
(`Mat2CayleyHamilton`) relates a matrix to its square.  Iteration — `Mⁿ`, the *dynamics* whose orbit
periods are the elliptic orders and whose growth is the hyperbolic boost — needs the one structural
law those readings presuppose: **multiplication is associative**.  This file proves it generally
(`ring_intZ`, not `decide`), propext-free.  With the `I2` identity (`decide` per use) `Mat2` is a
monoid; associativity is what makes `Mⁿ` well-defined and the trace recurrence
`tr(Mⁿ⁺¹) = tr·tr(Mⁿ) − det·tr(Mⁿ⁻¹)` (Cayley–Hamilton iterated) available.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)

/-- ★★★★ **`Mat2` multiplication is associative.**  `(M · N) · P = M · (N · P)` — the monoid law,
    proved generally by `ring_intZ` (propext-free via explicit entry rewrites). -/
theorem mul_assoc (M N P : Mat2) : Mat2.mul (Mat2.mul M N) P = Mat2.mul M (Mat2.mul N P) := by
  rcases M with ⟨a, b, c, d⟩
  rcases N with ⟨e, f, g, h⟩
  rcases P with ⟨i, j, k, l⟩
  have h1 : (a * e + b * g) * i + (a * f + b * h) * k
      = a * (e * i + f * k) + b * (g * i + h * k) := by ring_intZ
  have h2 : (a * e + b * g) * j + (a * f + b * h) * l
      = a * (e * j + f * l) + b * (g * j + h * l) := by ring_intZ
  have h3 : (c * e + d * g) * i + (c * f + d * h) * k
      = c * (e * i + f * k) + d * (g * i + h * k) := by ring_intZ
  have h4 : (c * e + d * g) * j + (c * f + d * h) * l
      = c * (e * j + f * l) + d * (g * j + h * l) := by ring_intZ
  show Mat2.mk ((a * e + b * g) * i + (a * f + b * h) * k)
        ((a * e + b * g) * j + (a * f + b * h) * l)
        ((c * e + d * g) * i + (c * f + d * h) * k)
        ((c * e + d * g) * j + (c * f + d * h) * l)
      = Mat2.mk (a * (e * i + f * k) + b * (g * i + h * k))
        (a * (e * j + f * l) + b * (g * j + h * l))
        (c * (e * i + f * k) + d * (g * i + h * k))
        (c * (e * j + f * l) + d * (g * j + h * l))
  rw [h1, h2, h3, h4]

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc
