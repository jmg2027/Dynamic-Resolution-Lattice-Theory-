# G125 — p-adic closure synthesis (post-merge harvest)

**Anchor**: the G123 p-adic follow-up closed the Teichmüller representative
`ω(x)` (diagonal limit + Frobenius fix), its uniqueness, the
`μ_{p−1} × (1+p·ℤ_p)` decomposition with `ZpSeqEquiv`-uniqueness, and
general (non-unit) division with correctness — all ∅-axiom.  Reading the
closure laterally surfaces the following.

## Patterns

- **Diagonal extraction is the universal p-adic limit constructor.**
  `invFull`, `sqrtFull`, and now `teichmuller` all share the template
  `limit.digits k := (approxSeq k).digits k`, where the approximant
  sequence is Cauchy (each step settles one more digit).  For
  `teichmuller` no separate digit-stability lemma was even needed — the
  Cauchy identity `teichmuller_iter_cauchy` *is* the diagonal's trunc
  recursion.  Candidate abstraction: a single `Zp.diagLimit (approx :
  Nat → ZpSeq) (hcauchy : …) : ZpSeq` with `diagLimit.trunc (n+1) =
  (approx n).trunc (n+1)`, instantiated by all three.
  (`Padic/Hensel`, `Padic/Teichmuller`.)

- **`frobenius_lift` is a uniqueness engine, not just a convergence tool.**
  `teichmuller_unique` proves two Frobenius-fixed lifts agreeing mod `p`
  agree at every level by the four-step chain
  `w₁ ≡ w₁^p ≡ w₂^p ≡ w₂ (mod p^(k+1))` — outer steps the fix, middle
  step `frobenius_lift`.  No Hensel-derivative bookkeeping.  General
  shape: *a lift map that raises agreement one level + a fixed-point
  property ⟹ uniqueness of the fixed point*.  Likely re-usable for any
  Hensel-lifted object with a contraction-like lift.

- **`ZpSeqEquiv` is the funext-free canonical equality; "sequence-level"
  questions are `ZpSeqEquiv` questions.**  `ZpSeqEquiv.of_trunc_all`
  (`SetoidFramework`) promotes *any* per-truncation result to the
  canonical equality with no funext (each digit a `Fin` equality, not a
  function equality).  Raw Lean `=` on `ZpSeq` needs funext and is a
  Lens artifact — not a 213 target.  This dissolves a whole class of
  "but is it true at the sequence level?" questions.

- **Pure-Nat-helper discipline keeps paying out.**  Several core Nat
  lemmas are propext-dirty (`Nat.mul_mod_mul_left`, `Nat.sub_add_cancel`,
  `Nat.mul_lt_mul_left`); the ∅-axiom replacements added this round
  (`mul_mod_mul_left_pure`, `sq_mod_of_succ`, `trunc_add_mod`) are
  generic and belong to the growing `Meta/Nat` toolkit.

## New questions

- **Sequence-level ring axioms (G123 direction C) are now a one-commit
  closure.**  The ring axioms hold at every `trunc n` (`Arith`); apply
  `ZpSeqEquiv.of_trunc_all` to get `ZpSeqEquiv (add x y) (add y x)` etc.
  — the "sequence-level" ring structure, funext-free.  C was filed as
  "high difficulty, needs propext"; the bridge retires that.

- **`i₅ = teichmuller(2-lift)` is now reachable.**  `i₅⁴ ≡ 1` (proved)
  gives `i₅⁵ ≡ i₅`, so `i₅` is Frobenius-fixed; by `teichmuller_unique`
  it equals the Teichmüller representative of `2 mod 5`.  A concrete
  "the 5-adic imaginary unit IS a Teichmüller representative" theorem,
  connecting `Hensel.i_5` to `TeichmullerUnit` rigorously (not just the
  μ₄ membership).

- **Generalise the uniqueness engine to sqrt.**  Does `sqrtFull`
  uniqueness (`sqr_unique_trunc`) fit the same lift+fixed-property
  template, or does it genuinely need the Hensel-derivative argument?
  If the former, a shared `unique_of_lift_fixed` lemma covers inverse,
  sqrt, and Teichmüller at once.

- **A `diagLimit` abstraction** (pattern 1) would let any future
  Cauchy p-adic construction land its limit object in ~5 lines instead
  of re-deriving the diagonal trunc recursion.

## Cross-references
`theory/math/numbersystems/padic_real213.md` (chapter),
`theory/essays/algebra/teichmuller_as_forced_fixed_point.md` (essay),
`lean/E213/Lib/Math/NumberSystems/Padic/{Teichmuller,TeichmullerUnit,SetoidFramework,Field,Arith}.lean`.
Live p-adic frontier: H in `G124_padic_drlt_5adic`; roadmap in
`G123_padic_next_directions`.
