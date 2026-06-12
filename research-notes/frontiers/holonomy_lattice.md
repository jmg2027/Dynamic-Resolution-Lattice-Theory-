# Holonomy of the lattice — open extensions

**Tier-1 frontier.**  The closed core: `lean/E213/Lib/Math/NumberSystems/Real213/
HolonomyLattice.lean` (25 PURE) + chapter `theory/math/analysis/holonomy_of_the_lattice.md`.
Holonomy = net transition around a closed loop of state-transitions (`holonomy :
List Mat2 → Mat2`); functoriality (`holonomy_append`), flatness (`det_holonomy_eq_one`,
`det = 1 = NS−NT`), the ℕ⁺ sector is loop-free (`positive_loop_trivial`, the
Stern–Brocot tree), holonomy born from the negation fold (`first_loop_is_the_fold`,
`[S,S] = −I`, order 4).  Three open directions:

1. **Full freeness of `⟨L, R⟩`** (the Stern–Brocot bijection).  Proven here only as
   *no-return* (`positive_loop_trivial`, via the strictly-growing entry-sum); the
   stronger *unique-word / faithful-monoid* statement (every positive matrix is a
   unique `L,R` word) needs the continued-fraction / odometer digit extraction —
   tie to `OdometerSternBrocotUnit` + `the_modular_geodesic_lens`.

2. **General order law `holonomy_pow`.**  `holonomy (List.replicate n S)` cycles
   with period 4; the general statement (a loop's holonomy has finite order ∈
   `{1,2,3,4,6}` iff its trace is in `{0,±1,±2}`) is exactly
   `FiniteOrderSpectrum.finite_order_spectrum` lifted to the holonomy fold — a
   short bridge, not yet written.

3. **Holonomy group as π₁ of the modular orbifold.**  The loop classes around the
   elliptic points `S` (order 4) and `U` (order 6); the holonomy group = the image
   of the path monoid = `PSL(2,ℤ) = ℤ₂ * ℤ₃`.  Connect to
   `theory/essays/analysis/the_modular_group_from_two_folds.md` and
   `the_modular_geodesic_lens`.

Closure record (proven side): `theory/math/analysis/holonomy_of_the_lattice.md`.
