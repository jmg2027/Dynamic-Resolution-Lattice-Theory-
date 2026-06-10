import E213.Meta.Int213.Core

/-!
# GaussTuple — the 4-axis tuple product, subtraction-free

The tuple-tower answer to "which operation does the imaginary unit
pop out of" (`research-notes/frontiers/numbersystem_square.md`
"Ontology: the tuple tower").

The inverse-marker pattern: `a+x=b` puts a `+`-inverse-marked `a` on
a new orthogonal axis (`x = (−1)a + b`); `ax=b` a ×-inverse-marked
one (`x = (1/a)·b`).  At `x^a = b` the pattern's prefix form breaks —
`^` is non-commutative, so the marker lodges *inside the exponent
slot* (`x = b^(1/a)`, the tuple `(b,(1,a))`).  The imaginary unit
arises from no single inverse axis: it pops out of the ×-fold
iterated on the unknown **aimed at the +-inverse axis**
(`x·x = the +-inverse unit`), the first question that composes two
inverse axes — and squaring is reflection-symmetric
(`CompletionDichotomy.int_sumSq_eq_zero`), so no combination of
existing axes reaches it: a genuinely new axis.

Under the product the imaginary axis drags the +-inverse axis into
the real component, so ℕ-coefficient pairs `(p,q)` are not ×-closed;
the closed object is the **4-axis nested tuple** `((a,b),(c,d))` —
real difference-pair, imaginary difference-pair.  `gmul` below is
that product written subtraction-free (every slot a bare ℕ-fold);
`gmul_i_i` shows `i ⊗ i` *is* the +-inverse unit (definitional), and
`gmul_readout` shows the tuple product reads out through the
difference-Lens to exactly the classical complex product — the
readout is a Lens on the tuple, not the tuple's identity.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.GaussTuple

open E213.Meta.Int213
  (subNatNat_mul_subNatNat subNatNat_add_subNatNat neg_subNatNat)

/-- The 4-axis tuple: ((real⁺, real⁻), (imag⁺, imag⁻)). -/
abbrev Gauss4 : Type := (Nat × Nat) × (Nat × Nat)

/-- The 4-axis product, subtraction-free.  Cross-wise bookkeeping of
    `(re·re − im·im, re·im + im·re)` with every minus absorbed into
    the pair axes. -/
def gmul : Gauss4 → Gauss4 → Gauss4
  | ((a, b), (c, d)), ((e, f), (g, h)) =>
    ((a*e + b*f + (c*h + d*g), a*f + b*e + (c*g + d*h)),
     (a*g + b*h + (c*e + d*f), a*h + b*g + (c*f + d*e)))

/-- The imaginary unit: nothing on the real axes, `(1,0)` on the
    imaginary difference-pair. -/
def iU : Gauss4 := ((0, 0), (1, 0))

/-- The +-inverse unit ("−1" as a tuple): `(0,1)` on the real
    difference-pair. -/
def negOne : Gauss4 := ((0, 1), (0, 0))

/-- ★★★★ `i ⊗ i` **is** the +-inverse unit — definitionally.  The
    question `x ⊗ x ≈ negOne` is solved by `iU` on the nose: the new
    axis folds back into the +-inverse axis at depth 2, which is why
    the axis count stops at two per component. -/
theorem gmul_i_i : gmul iU iU = negOne := rfl

/-- ★★★★★ **The tuple product reads out to the complex product.**
    Through the difference-Lens (`subNatNat` on each axis pair), the
    subtraction-free `gmul` is exactly
    `(x_re·y_re − x_im·y_im, x_re·y_im + x_im·y_re)`.
    Proof: the three Int213 keystones (`subNatNat_mul_subNatNat`,
    `neg_subNatNat`, `subNatNat_add_subNatNat`) and re-association. -/
theorem gmul_readout (a b c d e f g h : Nat) :
    (Int.subNatNat (a*e + b*f + (c*h + d*g)) (a*f + b*e + (c*g + d*h))
      = Int.subNatNat a b * Int.subNatNat e f
        + -(Int.subNatNat c d * Int.subNatNat g h))
    ∧ (Int.subNatNat (a*g + b*h + (c*e + d*f)) (a*h + b*g + (c*f + d*e))
      = Int.subNatNat a b * Int.subNatNat g h
        + Int.subNatNat c d * Int.subNatNat e f) := by
  constructor
  · rw [subNatNat_mul_subNatNat a b e f,
        subNatNat_mul_subNatNat c d g h,
        neg_subNatNat,
        subNatNat_add_subNatNat]
  · rw [subNatNat_mul_subNatNat a b g h,
        subNatNat_mul_subNatNat c d e f,
        subNatNat_add_subNatNat]

end E213.Lib.Math.NumberSystems.GaussTuple
