# 01 — The `ℤ[i]`-Lens counterexample (mathematical argument)

**Claim.** Under R1–R4 alone (as formalised in
`E213.Meta.LensCatalog`), the Gaussian-integer Lens

```
ziLens : Lens (ZI = ℤ[i])
  base_a  := i          (= ⟨0, 1⟩)
  base_b  := −i         (= ⟨0, -1⟩)
  combine := ZI.mul     (Gaussian multiplication)
```

satisfies R1, R2, R3, and R4. Since `ℤ[i]` is countable, and
`ℂ` (per Paper 1) is obtained by R1–R4 + R5 (requiring
cardinality ≥ `𝔠` via Cauchy-completeness), the uniqueness of
`ℂ` claimed in Paper 1 does not survive removal of R5.

## Verification

### R1 — Binary combine
By the `Lens` structure: `combine : ZI × ZI → ZI = ZI.mul`. ✓

### R2 — Recursive faithfulness + commutativity
`view := Raw.fold I (-I) ZI.mul` is a catamorphism by the
Firmware's `Raw.fold`. Commutativity of `ZI.mul` (needed to
descend from Tree to Raw, cf. Thm 3.2 of Paper 1) is
Lean-proved in `ZIDomain.mul_comm`. ✓

### R3 — NonVanishing (no zero divisors in the image)

**Lemma (Diophantus identity).** For all `u, v : ZI`,
`normSq (u * v) = normSq u * normSq v`, where
`normSq u := u.re² + u.im²`.

*Proof.* Expanding both sides:
```
normSq (u * v) = (ur vr − ui vi)² + (ur vi + ui vr)²
              = ur²vr² − 2 ur vr ui vi + ui²vi²
                + ur²vi² + 2 ur vi ui vr + ui²vr²
              = ur²(vr² + vi²) + ui²(vr² + vi²)
              = (ur² + ui²)(vr² + vi²)
              = normSq u · normSq v. ∎
```

**Lemma (norm zero iff zero).** `normSq u = 0 ↔ u = 0`.
*Proof.* Both `u.re²` and `u.im²` are non-negative in `ℤ`;
their sum is zero iff both are zero, iff `u.re = u.im = 0`. ∎

**R3.** Suppose `u ≠ 0` and `v ≠ 0`. Then `normSq u ≠ 0` and
`normSq v ≠ 0`. Since `ℤ` is an integral domain,
`normSq u · normSq v ≠ 0`, so `normSq (u * v) ≠ 0`, so
`u * v ≠ 0`. ✓

**R3 Lean-formalised** in `E213.Research.ZIDomain`:
`normSq_mul`, `normSq_nonneg`, `normSq_eq_zero_iff`,
`no_zero_div`, `mul_ne_zero_of_ne_zero`. Note: core Lean 4
has no `ring` tactic, so the Diophantus identity is closed by
`simp` with `Int.sub_mul`, `Int.add_mul`, `Int.mul_assoc`,
`Int.mul_comm`, `Int.mul_left_comm`, etc. (which AC-normalise
products) followed by `omega` for the final linear
cancellation of the `±abcd` cross terms.

### R4 — SwapMatching with `conj = ZI.conj`

**Lemma (conj is a ring homomorphism).** For all `u, v : ZI`,
`conj (u * v) = conj u * conj v`.

*Proof.* Write `u = ur + ui·i`, `v = vr + vi·i`.
```
u * v                  = (ur vr − ui vi) + (ur vi + ui vr) i
conj (u * v)           = (ur vr − ui vi) − (ur vi + ui vr) i
conj u · conj v        = (ur − ui i)(vr − vi i)
                       = ur vr − ur vi i − ui vr i + ui vi i²
                       = (ur vr − ui vi) − (ur vi + ui vr) i  ∎
```

**R4 proof (by induction on `r : Raw`).**

- *Base `r = a`:* `view (swap a) = view b = −i`;
  `conj (view a) = conj i = −i`. ✓
- *Base `r = b`:* `view (swap b) = view a = i`;
  `conj (view b) = conj (−i) = i`. ✓
- *Step `r = slash x y h`:*
  ```
  view (swap (slash x y h))
    = view (slash (swap x) (swap y) h')
    = ZI.mul (view (swap x)) (view (swap y))
    = ZI.mul (conj (view x)) (conj (view y))       [IH]
    = conj (ZI.mul (view x) (view y))              [conj hom]
    = conj (view (slash x y h)).
  ```
  ✓

Uniqueness of `conj`: `Aut_ℤ(ZI) = {id, ZI.conj}` — the only
nontrivial `ℤ`-algebra automorphism is complex conjugation.

## Consequence

`ziLens` is an admissible self-recognising Lens on `ZI` under
R1–R4. Since `ZI = ℤ[i]` is **countable** and is *not* an
ℝ-algebra (it is only a `ℤ`-algebra), the "codomain must be
ℝ-algebra" premise of Paper 1 §4.1 requires extra input — which
is precisely what R5 supplies in the paper.

**Hypothesis H confirmed (Lean-verified for R3 and R4).**

## Lean artifacts

- `E213.Research.ZI` — `ZI` structure, `mul`, `conj`, `normSq`,
  `conj_conj`, `conj_ne_id`.
- `E213.Research.ZIDomain` — `mul_comm`, `normSq_mul`,
  `normSq_nonneg`, `normSq_eq_zero_iff`, `no_zero_div`,
  `mul_ne_zero_of_ne_zero`.
- `E213.Research.ZIHom` — `conj_I`, `conj_negI`, `conj_mul`.
- `E213.Research.ZILens` —
  - `ziLens : Lens ZI`
  - `ziLens_nonVanishing : NonVanishing ziLens` (R3)
  - `ziLens_swapMatching : SwapMatching ziLens ZI.conj` (R4)
- `E213.Firmware.Raw.fold_swap_hom` — generic Raw-induction
  helper (enables R4 proof without Tree-internal access by
  the consumer).

## Remaining work

- E2: generalise to other quadratic extensions (`ℚ[i]`,
  `ℚ(√−2)`, `ℤ[ω]`, etc.). Each requires a codomain with
  `normSq` or equivalent multiplicative `ℤ`-valued norm.
- E3: formalise R5' (fold totality) as vacuous under inductive
  Raw.
- E4: hunt for the minimal extra condition that re-selects ℂ
  uniquely among quadratic extensions.
