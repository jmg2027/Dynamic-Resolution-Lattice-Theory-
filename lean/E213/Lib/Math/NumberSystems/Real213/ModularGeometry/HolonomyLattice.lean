import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace
import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc
import E213.Meta.Int213.Order

/-!
# Holonomy of a loop of state-transitions — and why the ℕ⁺ sector has none

## The bridge: state = state-transition (§6.6, §5.7)

Without external time, a *transition* is not separable from the *state* it
transitions to (`seed/AXIOM/06_lens_readings.md` §6.6).  A `Mat2` is exactly
this collapse made into a single object: read frozenly it is a configuration
(a lattice point — four counts); read dynamically it is the map `x ↦ M·x`.  The
**modular / Möbius matrix is the representation in which the two readings
coincide** — the operator *is* an object of the same kind, so a *loop of
transitions composes to a state of the same kind*.  That composite is the
**holonomy** of the loop.

`holonomy w` is the ordered fold-product of a path `w : List Mat2`.  Three facts
make it a holonomy in the genuine sense, all ∅-axiom:

  1. **Functoriality** (`holonomy_append`): `holonomy (p ++ q) = holonomy p ·
     holonomy q` — concatenation of paths composes their holonomies.  Holonomy
     is a monoid homomorphism from the free monoid of paths `(List Mat2, ++)` to
     the matrix monoid `(Mat2, ·)`.  The codomain is *states*: transport around
     a path lands on an object of the same kind it transported — the §6.6
     collapse, computational.

  2. **Flatness** (`det_holonomy_eq_one`): if every step has `det = 1` then the
     holonomy has `det = 1` around *every* loop.  `det = 1 = NS − NT` is the
     founding shared unit (`FoundingDynamicBridge`); it is the conserved
     holonomy invariant — the discrete "flat connection" whose curvature `det`
     is preserved by transport (the cross-determinant `−1` of `Mobius213` is the
     same invariant read on the convergent pair).

  3. **The ℕ⁺ sector is loop-free; holonomy is *born from the fold*.**  The
     Stern–Brocot / Calkin–Wilf generators `L = [[1,0],[1,1]]`,
     `R = [[1,1],[0,1]]` have entries in ℕ — the ℕ⁺ sector — and `det = 1`.
     Every **non-empty** positive word strictly grows its entry-sum
     (`positiveWord_entrySum_gt_two`), so it never returns to `I`
     (`positive_loop_trivial`): the positive monoid `⟨L, R⟩` has **no
     non-trivial loop** — it is a tree (the Stern–Brocot simply-connected side
     of the modular tessellation).  A non-trivial loop appears **exactly when the
     negation-fold composite `S = N·R` is admitted**: `S` carries the `−1`
     (`S.b = −1`) the ℕ⁺ sector excludes, and `holonomy [S, S] = −I ≠ I` is the
     first closed loop (`first_loop_is_the_fold`), of order 4 — the elliptic
     Gaussian period.  Holonomy is the obstruction the difference-Lens (ℤ, the
     sign fold of §6.7) creates and the count-Lens (ℕ⁺) cannot.

So "dynamic" (a loop of transitions) read as a lattice (positive-integer
matrices) has *trivial* holonomy; holonomy is the residue-internal signature of
the fold that turns ℕ⁺ into ℤ.

All theorems ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc (mul_assoc)
open E213.Meta.Int213.Order

/-! ## §1 — coefficient collapses + `Mat2` identity laws (the monoid units)

`ring_intZ` normalises ℤ-polynomials but does not fold the `0·x` / `1·x`
coefficients of the `0/1`-entry generators; these three explicit collapses do,
all propext-free. -/

private theorem c00 (x y : Int) : 1 * x + 0 * y = x := by
  rw [E213.Meta.Int213.PolyIntM.one_mulZ, E213.Meta.Int213.zero_mul, Int.add_zero]

private theorem c01 (x y : Int) : 0 * x + 1 * y = y := by
  rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.PolyIntM.one_mulZ,
      E213.Meta.Int213.zero_add]

private theorem c11 (x y : Int) : 1 * x + 1 * y = x + y := by
  rw [E213.Meta.Int213.PolyIntM.one_mulZ, E213.Meta.Int213.PolyIntM.one_mulZ]

/-- `I · M = M`. -/
theorem one_mul (M : Mat2) : Mat2.mul Mat2.I M = M := by
  rcases M with ⟨a, b, c, d⟩
  show Mat2.mk (1 * a + 0 * c) (1 * b + 0 * d) (0 * a + 1 * c) (0 * b + 1 * d)
      = Mat2.mk a b c d
  rw [c00 a c, c00 b d, c01 a c, c01 b d]

/-! ## §2 — Holonomy: the net transition around a path

`holonomy [g₀, g₁, …, gₙ] = g₀ · g₁ · … · gₙ · I` — the ordered fold-product.
A *path* is a `List Mat2` of state-transitions; the holonomy is the single
state-transition (= state, §6.6) they compose to. -/

/-- The holonomy (net transition) of a path. -/
def holonomy : List Mat2 → Mat2
  | [] => Mat2.I
  | g :: gs => Mat2.mul g (holonomy gs)

@[simp] theorem holonomy_nil : holonomy [] = Mat2.I := rfl

@[simp] theorem holonomy_cons (g : Mat2) (gs : List Mat2) :
    holonomy (g :: gs) = Mat2.mul g (holonomy gs) := rfl

/-- ★★★★ **Functoriality of holonomy** — the path-composition law.
    `holonomy (p ++ q) = holonomy p · holonomy q`.  Concatenating paths composes
    their holonomies: holonomy is a monoid homomorphism from the free monoid of
    paths `(List Mat2, ++, [])` to the matrix monoid `(Mat2, ·, I)`.  This is the
    §6.6 collapse made computational — a loop of *transitions* composes to a
    single *state* of the same kind. -/
theorem holonomy_append (p q : List Mat2) :
    holonomy (p ++ q) = Mat2.mul (holonomy p) (holonomy q) := by
  induction p with
  | nil =>
    show holonomy q = Mat2.mul (holonomy []) (holonomy q)
    rw [holonomy_nil, one_mul]
  | cons g gs ih =>
    show Mat2.mul g (holonomy (gs ++ q))
        = Mat2.mul (Mat2.mul g (holonomy gs)) (holonomy q)
    rw [ih]
    exact (mul_assoc g (holonomy gs) (holonomy q)).symm

/-! ## §3 — Flatness: `det = 1` is the conserved holonomy invariant -/

/-- `det` is multiplicative (Cauchy–Binet for `2×2`): `det (M · N) = det M · det N`. -/
theorem det_mul (M N : Mat2) :
    Mat2.det (Mat2.mul M N) = Mat2.det M * Mat2.det N := by
  rcases M with ⟨a, b, c, d⟩
  rcases N with ⟨e, f, g, h⟩
  show (a * e + b * g) * (c * f + d * h) - (a * f + b * h) * (c * e + d * g)
      = (a * d - b * c) * (e * h - f * g)
  ring_intZ

/-- ★★★ **Flat holonomy.**  If every step of the path has `det = 1`, the
    holonomy has `det = 1` around the *whole* loop.  `det = 1 = NS − NT` is the
    founding shared unit (`FoundingDynamicBridge`): the conserved invariant of
    transport — the discrete flat connection.  Proof: `det` is multiplicative
    and `det I = 1`. -/
theorem det_holonomy_eq_one :
    ∀ (w : List Mat2), (∀ g, g ∈ w → Mat2.det g = 1) → Mat2.det (holonomy w) = 1
  | [], _ => by decide
  | g :: gs, h => by
    rw [holonomy_cons, det_mul, h g (List.Mem.head gs),
        det_holonomy_eq_one gs (fun x hx => h x (List.Mem.tail g hx))]
    decide

/-! ## §4 — The ℕ⁺ generators and the entry-sum length functional

`L = [[1,0],[1,1]]`, `R = [[1,1],[0,1]]` — the Stern–Brocot / Calkin–Wilf
generators, entries in ℕ (the ℕ⁺ sector), `det = 1`.  Every positive rational is
reached by a unique word in `L, R` (the tree); the holonomy below shows that
tree has no loop. -/

/-- The ℕ⁺ generator `L` (Stern–Brocot left). -/
def L : Mat2 := ⟨1, 0, 1, 1⟩
/-- The ℕ⁺ generator `R` (Stern–Brocot right). -/
def R : Mat2 := ⟨1, 1, 0, 1⟩

/-- Both generators have `det = 1` (the flat invariant) and lie in the ℕ⁺ sector
    (all entries `≥ 0`), unlike the fold-composite `S` whose `b`-entry is `−1`. -/
theorem generators_det_one : Mat2.det L = 1 ∧ Mat2.det R = 1 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The entry-sum — a length functional on the lattice. `entrySum I = 2`. -/
def entrySum (M : Mat2) : Int := M.a + M.b + M.c + M.d

/-- `M` is in the **positive interior**: diagonal `≥ 1`, off-diagonal `≥ 0`.
    `I, L, R` are positive, and the property is preserved by left-multiplication
    by `L` or `R`. -/
def Pos (M : Mat2) : Prop := 1 ≤ M.a ∧ 0 ≤ M.b ∧ 0 ≤ M.c ∧ 1 ≤ M.d

theorem pos_I : Pos Mat2.I := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `L · M` in clean entry form: `⟨a, b, a+c, b+d⟩`. -/
theorem mul_L_eq (M : Mat2) :
    Mat2.mul L M = ⟨M.a, M.b, M.a + M.c, M.b + M.d⟩ := by
  rcases M with ⟨a, b, c, d⟩
  show Mat2.mk (1 * a + 0 * c) (1 * b + 0 * d) (1 * a + 1 * c) (1 * b + 1 * d)
      = Mat2.mk a b (a + c) (b + d)
  rw [c00 a c, c00 b d, c11 a c, c11 b d]

/-- `R · M` in clean entry form: `⟨a+c, b+d, c, d⟩`. -/
theorem mul_R_eq (M : Mat2) :
    Mat2.mul R M = ⟨M.a + M.c, M.b + M.d, M.c, M.d⟩ := by
  rcases M with ⟨a, b, c, d⟩
  show Mat2.mk (1 * a + 1 * c) (1 * b + 1 * d) (0 * a + 1 * c) (0 * b + 1 * d)
      = Mat2.mk (a + c) (b + d) c d
  rw [c11 a c, c11 b d, c01 a c, c01 b d]

/-! ## §5 — `Pos` is preserved; the entry-sum strictly grows -/

private theorem zero_lt_of_one_le {x : Int} (hx : 1 ≤ x) : (0 : Int) < x :=
  lt_of_lt_of_le (by decide) hx

private theorem lt_add_pos (x p : Int) (hp : 0 < p) : x < x + p :=
  lt_of_sub_pos (by rw [show (x + p) - x = p by ring_intZ]; exact hp)

private theorem zero_le_of_one_le {x : Int} (hx : 1 ≤ x) : (0 : Int) ≤ x :=
  le_of_lt (zero_lt_of_one_le hx)

private theorem one_le_add_of {x y : Int} (hx : 1 ≤ x) (hy : 0 ≤ y) : 1 ≤ x + y := by
  apply le_of_sub_nonneg
  rw [show x + y - 1 = (x - 1) + y by ring_intZ]
  exact nonneg_of_le_zero
    (E213.Meta.Int213.add_nonneg (le_zero_of_nonneg (sub_nonneg_of_le hx)) hy)

private theorem one_le_add_of' {x y : Int} (hx : 0 ≤ x) (hy : 1 ≤ y) : 1 ≤ x + y := by
  rw [show x + y = y + x by ring_intZ]; exact one_le_add_of hy hx

private theorem zero_le_add {x y : Int} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y :=
  E213.Meta.Int213.add_nonneg hx hy

theorem pos_mul_L {M : Mat2} (h : Pos M) : Pos (Mat2.mul L M) := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  rw [mul_L_eq]
  exact ⟨ha, hb, zero_le_add (zero_le_of_one_le ha) hc, one_le_add_of' hb hd⟩

theorem pos_mul_R {M : Mat2} (h : Pos M) : Pos (Mat2.mul R M) := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  rw [mul_R_eq]
  exact ⟨one_le_add_of ha hc, zero_le_add hb (zero_le_of_one_le hd), hc, hd⟩

theorem entrySum_mul_L (M : Mat2) :
    entrySum (Mat2.mul L M) = entrySum M + (M.a + M.b) := by
  rw [mul_L_eq]
  show M.a + M.b + (M.a + M.c) + (M.b + M.d)
      = (M.a + M.b + M.c + M.d) + (M.a + M.b)
  ring_intZ

theorem entrySum_mul_R (M : Mat2) :
    entrySum (Mat2.mul R M) = entrySum M + (M.c + M.d) := by
  rw [mul_R_eq]
  show (M.a + M.c) + (M.b + M.d) + M.c + M.d
      = (M.a + M.b + M.c + M.d) + (M.c + M.d)
  ring_intZ

theorem entrySum_lt_L {M : Mat2} (h : Pos M) :
    entrySum M < entrySum (Mat2.mul L M) := by
  rw [entrySum_mul_L]
  exact lt_add_pos _ _ (zero_lt_of_one_le (one_le_add_of h.1 h.2.1))

theorem entrySum_lt_R {M : Mat2} (h : Pos M) :
    entrySum M < entrySum (Mat2.mul R M) := by
  rw [entrySum_mul_R]
  exact lt_add_pos _ _ (zero_lt_of_one_le (one_le_add_of' h.2.2.1 h.2.2.2))

theorem entrySum_ge_two {M : Mat2} (h : Pos M) : (2 : Int) ≤ entrySum M := by
  obtain ⟨ha, hb, hc, hd⟩ := h
  apply le_of_sub_nonneg
  rw [show entrySum M - 2 = (M.a - 1) + (M.d - 1) + M.b + M.c by
        show (M.a + M.b + M.c + M.d) - 2 = _; ring_intZ]
  exact nonneg_of_le_zero
    (zero_le_add (zero_le_add (zero_le_add
      (le_zero_of_nonneg (sub_nonneg_of_le ha))
      (le_zero_of_nonneg (sub_nonneg_of_le hd))) hb) hc)

/-! ## §6 — The ℕ⁺ sector is loop-free (the Stern–Brocot tree) -/

/-- A path lies in the ℕ⁺ sector when every step is a Stern–Brocot generator. -/
def PositiveWord (w : List Mat2) : Prop := ∀ g, g ∈ w → g = L ∨ g = R

/-- The holonomy of a positive word is always in the positive interior. -/
theorem holonomy_pos : ∀ (w : List Mat2), PositiveWord w → Pos (holonomy w)
  | [], _ => pos_I
  | g :: gs, hw => by
    have hg : g = L ∨ g = R := hw g (List.Mem.head gs)
    have hgs : Pos (holonomy gs) :=
      holonomy_pos gs (fun x hx => hw x (List.Mem.tail g hx))
    rw [holonomy_cons]
    rcases hg with hL | hR
    · rw [hL]; exact pos_mul_L hgs
    · rw [hR]; exact pos_mul_R hgs

/-- ★★★ **Non-empty positive loops strictly grow.**  Every non-empty word in the
    ℕ⁺ generators has holonomy entry-sum `> 2 = entrySum I` — the length
    functional strictly increases at every step, so the path cannot have
    returned to its start. -/
theorem positiveWord_entrySum_gt_two :
    ∀ (w : List Mat2), PositiveWord w → w ≠ [] → (2 : Int) < entrySum (holonomy w)
  | [], _, hne => absurd rfl hne
  | g :: gs, hw, _ => by
    have hg : g = L ∨ g = R := hw g (List.Mem.head gs)
    have hgs : Pos (holonomy gs) :=
      holonomy_pos gs (fun x hx => hw x (List.Mem.tail g hx))
    rw [holonomy_cons]
    rcases hg with hL | hR
    · rw [hL]; exact lt_of_le_of_lt (entrySum_ge_two hgs) (entrySum_lt_L hgs)
    · rw [hR]; exact lt_of_le_of_lt (entrySum_ge_two hgs) (entrySum_lt_R hgs)

/-- ★★★★ **The ℕ⁺ sector has no non-trivial loop.**  No non-empty positive word
    returns to the identity: `holonomy w ≠ I`.  The Stern–Brocot monoid `⟨L, R⟩`
    is free — a tree, simply connected — so the count-Lens (ℕ⁺) sees only
    trivial holonomy. -/
theorem positive_loop_trivial {w : List Mat2}
    (hw : PositiveWord w) (hne : w ≠ []) : holonomy w ≠ Mat2.I := by
  intro hEq
  have h2 : (2 : Int) < entrySum (holonomy w) := positiveWord_entrySum_gt_two w hw hne
  rw [hEq] at h2
  have hI : entrySum Mat2.I = (2 : Int) := by decide
  rw [hI] at h2
  exact lt_irrefl 2 h2

/-! ## §7 — Holonomy is born from the fold (ℤ, the sign-Lens of §6.7)

The first non-trivial closed loop appears exactly when the negation-fold
composite `S = N·R = z ↦ −1/z` is admitted.  `S` carries the `−1` the ℕ⁺ sector
excludes; `[S, S]` is the first loop, returning to `−I` (order 4, the elliptic
Gaussian period), while no positive word ever closes. -/

/-- ★★★★ **The first non-trivial loop is the fold.**  `holonomy [S, S] = −I ≠ I`
    (the length-2 fold loop closes onto the central element, order 4), whereas
    the length-2 positive loop `[L, R]` does **not** close
    (`positive_loop_trivial`).  The `−1` entry `S.b = −1` is what the ℕ⁺ sector
    lacks: holonomy is the signature of the sign fold ℕ⁺ → ℤ (§6.7). -/
theorem first_loop_is_the_fold :
    holonomy [Mat2.S, Mat2.S] = Mat2.negI
    ∧ holonomy [Mat2.S, Mat2.S, Mat2.S, Mat2.S] = Mat2.I
    ∧ Mat2.negI ≠ Mat2.I
    ∧ Mat2.S.b = -1
    ∧ holonomy [L, R] ≠ Mat2.I := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide


/-- ★ **Determinant is multiplicative over holonomy concatenation**:
    `det(holonomy (p ++ q)) = det(holonomy p) · det(holonomy q)` — `det∘holonomy` is a
    monoid homomorphism `(List Mat2, ++) → (ℤ, ·)`. -/
theorem det_holonomy_append (p q : List Mat2) :
    Mat2.det (holonomy (p ++ q)) = Mat2.det (holonomy p) * Mat2.det (holonomy q) := by
  rw [holonomy_append, det_mul]
end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
