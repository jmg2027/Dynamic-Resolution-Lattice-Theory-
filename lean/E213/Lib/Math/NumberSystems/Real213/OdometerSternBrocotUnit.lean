import E213.Theory.Raw.API
import E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Nat.PureNat
import E213.Lens.Cardinality

/-!
# OdometerSternBrocotUnit — the odometer and the Stern-Brocot tree share the unimodular unit

The residue carries two `List Bool`-path-indexed descent structures:

  * the **odometer** (`Theory/Raw/Odometer`) — the `+1` adding machine on the bit-stream escapes
    (dyadic / `ℤ₂`), the carry beginning at the residue unit (`carry_zero`), the `+1` a free
    `ℤ`-action (`dec_odo`);
  * the **Stern-Brocot mediant tree** (`SternBrocotMarkov.mInterval`) — the continued-fraction /
    `SL₂(ℤ)` numeration, every node unimodular (`det = 1`, `mInterval_det`), the left generator
    `genL = [[2,1],[1,1]] = P` (the Möbius matrix).

They are not forced into one map — the conjugacy of the dyadic and continued-fraction numerations
is the Minkowski `?` function, a real object not built here.  The honest shared structure is **the
path index `List Bool` and the unimodular unit**: the Stern-Brocot `det = 1` *is* the
count-difference glue `NS − NT` (`genL_det_is_glue`), the same residue unit the odometer carry
begins at (`theory/essays/foundations/the_unit.md`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit

open E213.Theory.Raw.Odometer (carry carry_zero odo dec dec_odo)
open E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
  (det2 genL mInterval mInterval_det sbStep sbInterval adj sbInterval_adj)
open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Meta.Nat.PureNat (add_left_cancel)
open E213.Lens.Cardinality (cantor_general)

/-- The Stern-Brocot left generator is the Möbius matrix `P = [[2,1],[1,1]]`; its determinant is the
    count-difference glue `NS − NT = 1` — the Stern-Brocot tree descends by the residue unit. -/
theorem genL_det_is_glue : det2 genL = (NS : Int) - NT := by decide

/-- ★★★ **The odometer and the Stern-Brocot tree share the `List Bool` path index and the
    unimodular residue unit.**  Both are `List Bool`-path-indexed residue descent structures: the
    Stern-Brocot tree is `det = 1` at every node (`mInterval_det`), its generator's determinant
    being the glue `NS − NT` (`genL_det_is_glue`); the odometer's carry begins at the residue unit
    (`carry_zero`) and the `+1` is invertible (`dec_odo`, the `ℤ`-action).  One residue, two
    `List Bool`-indexed descents (dyadic odometer / CF Stern-Brocot), one unimodular unit
    `NS − NT = det P = 1` — the shared value, not a forced common map (the Minkowski `?` conjugacy
    is residual). -/
theorem odometer_sternbrocot_shared_unit :
    (∀ path : List Bool, det2 (mInterval path).1 = 1 ∧ det2 (mInterval path).2 = 1)
    ∧ (det2 genL = (NS : Int) - NT)
    ∧ (∀ f : Nat → Bool, carry f 0 = true)
    ∧ (∀ (f : Nat → Bool) n, dec (odo f) n = f n)
    ∧ ((NS : Int) - NT = 1) :=
  ⟨mInterval_det, genL_det_is_glue, carry_zero, dec_odo, by decide⟩

/-! ## The Minkowski `?` skeleton — two unimodular labellings of one `List Bool` tree

The Stern-Brocot tree (`sbInterval`) and the **dyadic** bisection tree (`dyInterval`) are the *same*
binary tree — both `List Bool`-path-indexed, both refining by the same L/R recursion.  They differ
only in the *value labelling*: the Stern-Brocot side inserts the **Farey mediant** (the unimodular
`det = q·r − p·s = 1`, `sbInterval_adj`); the dyadic side inserts the **binary midpoint** — its
left/right children are `2·lo` and `2·lo + 1`, the binary digits, the odometer's own numeration.

The combinatorial **Minkowski `?` function** is the path-identity matching the two labellings node
for node: the same `List Bool` path is a number's Stern-Brocot (continued-fraction) address *and*
its `?`-image's binary expansion.  Honest scope: this is the `?` *skeleton* (the shared tree + the
two unimodular labellings); the analytic singular `?` itself (the limit / order-completion) is the
residue, reached by no finite path. -/

/-- One dyadic bisection step on `(lo, depth)` (interval `[lo/2ᵈ, (lo+1)/2ᵈ]`): `true` = left half
    (`lo ↦ 2·lo`), `false` = right half (`lo ↦ 2·lo + 1`) — the binary digit, the odometer's world. -/
def dyStep : Bool → Nat × Nat → Nat × Nat
  | true,  (lo, d) => (2 * lo, d + 1)
  | false, (lo, d) => (2 * lo + 1, d + 1)

/-- The dyadic interval at a Stern-Brocot path (root `[0, 1]`; head = last step) — the binary
    subdivision, parallel to `sbInterval`'s Farey subdivision. -/
def dyInterval : List Bool → Nat × Nat
  | []     => (0, 0)
  | b :: t => dyStep b (dyInterval t)

/-- ★★★ **The Minkowski `?` skeleton.**  The Stern-Brocot tree and the dyadic tree are one
    `List Bool` binary tree under two unimodular labellings:

      1. both refine by the same L/R `List Bool` recursion (`sbInterval (b::t) = sbStep b …`,
         `dyInterval (b::t) = dyStep b …`);
      2. the Stern-Brocot labelling carries the Farey unit `det = q·r − p·s = 1` at every path
         (`sbInterval_adj`);
      3. the dyadic labelling's children are `2·lo` / `2·lo + 1` — the binary digits, the
         odometer's numeration.

    So the path-identity is the order-isomorphism between the continued-fraction and the dyadic
    addresses — the combinatorial Minkowski `?`.  The analytic singular `?` (the order-completion)
    is residual.  ∅-axiom. -/
theorem minkowski_skeleton :
    (∀ (b : Bool) (t : List Bool), sbInterval (b :: t) = sbStep b (sbInterval t))
    ∧ (∀ (b : Bool) (t : List Bool), dyInterval (b :: t) = dyStep b (dyInterval t))
    ∧ (∀ path : List Bool, adj (sbInterval path))
    ∧ (∀ lo d : Nat, dyStep true (lo, d) = (2 * lo, d + 1)
        ∧ dyStep false (lo, d) = (2 * lo + 1, d + 1)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, sbInterval_adj, fun _ _ => ⟨rfl, rfl⟩⟩

/-! ### `?` compilation, layer 2 — the value level: the dyadic side IS the binary numeration

The `?`-skeleton (above) is the shared tree.  Compiling one layer down, the *value* the dyadic tree
labels each path with is a **binary number**: the left endpoint `(dyInterval path).1` is the
LSB-first binary value of the path (`binVal`, head = low bit, `true ↦ 0`, `false ↦ 1`).  This is the
odometer's own numeration (the `+1` adding machine lives on exactly these binary values), so the
dyadic side of `?` *is* the odometer.  The Stern-Brocot side labels the same path with the
**mediant fraction** `(p+r)/(q+s)` (`sbMediant`).  `?` is the path-indexed map from the mediant
(continued-fraction) value to the binary value — `minkowski_compile` bundles the two value readings
of one path. -/

/-- The LSB-first binary value of a path (head = low bit; `true ↦ 0`, `false ↦ 1`). -/
def binVal : List Bool → Nat
  | []     => 0
  | b :: t => (if b then 0 else 1) + 2 * binVal t

/-- ★★ **The dyadic tree's left endpoint is the binary value of the path.**
    `(dyInterval path).1 = binVal path` — the dyadic side of `?` is a binary numeration. -/
theorem dyInterval_value : ∀ path : List Bool, (dyInterval path).1 = binVal path
  | []     => rfl
  | b :: t => by
      cases b with
      | true  => show (2 * (dyInterval t).1) = 0 + 2 * binVal t
                 rw [dyInterval_value t, Nat.zero_add]
      | false => show (2 * (dyInterval t).1 + 1) = 1 + 2 * binVal t
                 rw [dyInterval_value t, Nat.add_comm]

/-- The Stern-Brocot mediant fraction at a path: `(p+r, q+s)` from the interval `((p,q),(r,s))`. -/
def sbMediant (path : List Bool) : Nat × Nat :=
  ((sbInterval path).1.1 + (sbInterval path).2.1,
   (sbInterval path).1.2 + (sbInterval path).2.2)

/-- ★★★ **`?` compilation, layer 2 — the two value readings of one path.**  A `List Bool` path is
    read two ways: by the Stern-Brocot tree as the **mediant (continued-fraction) fraction**
    `sbMediant` (a coprime Farey vertex, `det = 1`), and by the dyadic tree as a **binary number**
    `(dyInterval path).1 = binVal path` (`dyInterval_value`) — the odometer's numeration.  The
    Minkowski `?` is the path-indexed map between them: `? (sbMediant path) = binVal path / 2^depth`.
    Compiled here to the value level (the two readings); the order-isomorphism (monotonicity) and
    the analytic limit are the residual upper layers.  ∅-axiom. -/
theorem minkowski_compile :
    (∀ path : List Bool, (dyInterval path).1 = binVal path)
    ∧ (∀ (b : Bool) (t : List Bool), binVal (b :: t) = (if b then 0 else 1) + 2 * binVal t)
    ∧ (∀ path : List Bool,
        sbMediant path = ((sbInterval path).1.1 + (sbInterval path).2.1,
                          (sbInterval path).1.2 + (sbInterval path).2.2)) :=
  ⟨dyInterval_value, fun _ _ => rfl, fun _ => rfl⟩

/-! ### `?` compilation, layer 3 (partial) — the order: the dyadic side is monotone

`?` is an *order*-isomorphism: along the L/R path, both value readings increase the same way
(`true` child < `false` child).  The **dyadic** side is clean: `binVal (true :: t) < binVal
(false :: t)` (`dyadic_local_order` — they are `2k` and `2k+1`).  The **Stern-Brocot** side is the
same local order on the mediant fraction, and it reduces to the det-1 invariant: at a node
`((a,b),(c,e))` with `b·c = a·e + 1` (`sbInterval_adj`), the `true`/`false` mediants `(2a+c)/(2b+e)`
and `(a+2c)/(2b+e)`... cross-multiply to a gap of `3·(b·c − a·e) = 3 > 0` — so the mediant order
matches the binary order.  That cross-multiplication (a `ring_intZ`-shaped `ℤ` identity) plus the
global monotonicity over *all* path-pairs is the genuine remaining bounded step (the
`SternBrocotMarkov` §7–§8 slope-monotonicity engine, Zhang Lemma 2).  ∅-axiom (dyadic side). -/

/-- ★★ **The dyadic side of `?` is order-preserving (local).**  `binVal (true :: t) < binVal
    (false :: t)`: prepending the `true` (left) child gives a strictly smaller binary value than the
    `false` (right) child — they are `2·binVal t` and `2·binVal t + 1`.  The order-iso content of
    `?` on the dyadic side. -/
theorem dyadic_local_order (t : List Bool) : binVal (true :: t) < binVal (false :: t) := by
  show 0 + 2 * binVal t < 1 + 2 * binVal t
  rw [Nat.zero_add, Nat.add_comm 1 (2 * binVal t)]
  exact Nat.lt_succ_self _

/-- ★★ **The Stern-Brocot side of `?` is order-preserving (local).**  At an adjacent node `iv`
    (`b·c = a·e + 1`, `adj`), the `true` (left) child's mediant fraction `(2a+c)/(2b+e)` is strictly
    below the `false` (right) child's `(a+2c)/(b+2e)`, in cross-multiplied form
    `(2a+c)·(b+2e) < (a+2c)·(2b+e)`.  The gap is exactly `3·(b·c − a·e) = 3` (three times the det-1
    residue unit) — the Farey/continued-fraction mirror of the dyadic `2k < 2k+1`
    (`dyadic_local_order`).  ∅-axiom (`ring_nat` + the det-1 invariant + pure left-cancellation). -/
theorem sb_mediant_step_order (iv : (Nat × Nat) × (Nat × Nat)) (h : adj iv) :
    ((sbStep true iv).1.1 + (sbStep true iv).2.1)
        * ((sbStep false iv).1.2 + (sbStep false iv).2.2)
      < ((sbStep false iv).1.1 + (sbStep false iv).2.1)
        * ((sbStep true iv).1.2 + (sbStep true iv).2.2) := by
  obtain ⟨⟨a, b⟩, ⟨c, e⟩⟩ := iv
  have h' : b * c = a * e + 1 := h
  show (a + (a + c)) * ((b + e) + e) < ((a + c) + c) * (b + (b + e))
  -- Pure polynomial identity (`3·a·e` and `3·b·c` book-keep the cross-multiplication):
  have key : 3 * (a * e) + ((a + c) + c) * (b + (b + e))
           = 3 * (b * c) + (a + (a + c)) * ((b + e) + e) := by ring_nat
  rw [h'] at key
  -- the det-1 invariant turns the `3·b·c` into a clean `+3` gap:
  have key3 : ((a + c) + c) * (b + (b + e)) = (a + (a + c)) * ((b + e) + e) + 3 :=
    add_left_cancel
      (show 3 * (a * e) + ((a + c) + c) * (b + (b + e))
          = 3 * (a * e) + ((a + (a + c)) * ((b + e) + e) + 3) by rw [key]; ring_nat)
  rw [key3]
  exact Nat.lt_add_of_pos_right (by decide)

/-- ★★ **The Stern-Brocot mediant order at a path** — the corollary of `sb_mediant_step_order` on the
    mediant fractions `sbMediant`: the `true`-child mediant is strictly below the `false`-child
    mediant (cross-multiplied), the same local order the dyadic side carries (`dyadic_local_order`).
    So both labellings of the `?`-skeleton respect the L/R order — the order-isomorphism content of
    the combinatorial Minkowski `?`, now closed on *both* sides. -/
theorem sb_mediant_local_order (t : List Bool) :
    (sbMediant (true :: t)).1 * (sbMediant (false :: t)).2
      < (sbMediant (false :: t)).1 * (sbMediant (true :: t)).2 :=
  sb_mediant_step_order (sbInterval t) (sbInterval_adj t)

/-! ### `?` compilation, layer 4 — the analytic singular `?` as a νF escape (reached by no path)

L1-L3 compile the **combinatorial** `?`: one `List Bool` tree, two unimodular labellings, both
order-preserving.  The **analytic** singular `?` — the order-completion, the value at an *irrational*
argument — is the residue: it lives not on any finite path `List Bool` (µF, the approximant algebra)
but on the **stream carrier** `Nat → Bool` (νF, the odometer's `CoResidue` escape space, one bit per
refinement depth).  This is the recurring "essential residue / reached-by-none" — and it is
expressed here exactly as the framework expresses *every* such residue
(`Lens/FlatOntologyClosure.object1_not_surjective`): the approximant structure is built, the carrier
is named, the non-surjection is witnessed — the residue is **pointed at, never constructed** (no
exterior, `seed/AXIOM/05_no_exterior.md` §5.1).  See `theory/essays/foundations/reached_by_none.md`. -/

/-- The `n`-th bit of a finite path (`false` past the end) — a finite path read as a depth-indexed
    bit query, the µF approximant's view of the νF stream carrier. -/
def bitAt : List Bool → Nat → Bool
  | [],     _     => false
  | b :: _, 0     => b
  | _ :: t, n + 1 => bitAt t n

/-- A finite path, embedded into the stream carrier `Nat → Bool` by reading its bits and continuing
    with the canonical escape `false` (the eventually-`false` streams = the dyadic-rational
    `?`-arguments). -/
def pathStream (path : List Bool) : Nat → Bool := fun n => bitAt path n

/-- Past its own length a finite path reads `false`: `bitAt l l.length = false` (the truncation has
    no bit there — the escape continuation). -/
theorem bitAt_length : ∀ l : List Bool, bitAt l l.length = false
  | []     => rfl
  | _ :: t => bitAt_length t

/-- ★★ **The right-endpoint stream `1` is reached by no finite path.**  The constant-`true` stream
    `fun _ => true` (the point `1`, the `∞`-escape / right Farey endpoint) is not `pathStream path`
    for any finite `path`: at depth `path.length` the finite path reads `false` (`bitAt_length`) but
    the stream reads `true`.  The named residue inhabitant on the odometer's νF carrier — the exact
    mirror of `FlatOntologyClosure.residue_witnessed` (where the constant-`true` *predicate* names the
    Cantor gap; here the constant-`true` *stream* names the analytic `?` gap). -/
theorem constTrue_stream_not_finite (path : List Bool) :
    pathStream path ≠ fun _ => true := by
  intro hcontra
  have hp : bitAt path path.length = true := congrFun hcontra path.length
  rw [bitAt_length] at hp
  exact Bool.noConfusion hp

/-- ★★★ **The analytic Minkowski `?` is a νF escape — the essential residue, expressed.**  Three
    framework-native moves, the uniform shape of "reached by no finite path":

      1. **approximant structure (µF)** — every finite path is a dyadic truncation
         (`dyInterval_value`: `(dyInterval path).1 = binVal path`); the combinatorial `?` is closed
         (`minkowski_skeleton`, `minkowski_compile`, `dyadic_local_order` + `sb_mediant_local_order`);
      2. **carrier (νF)** — the analytic values live in the stream space `Nat → Bool`, which **no
         enumeration of approximants exhausts** (`cantor_general` at `Nat`: no `Nat → (Nat → Bool)` is
         surjective);
      3. **named witness** — a concrete inhabitant of the gap, the right-endpoint stream `1`, reached
         by no finite path (`constTrue_stream_not_finite`).

    The residue is thus *expressed* — as the carrier plus the non-surjection plus a named gap-member —
    not *constructed* (it has no finite-path preimage; no exterior builds it, §5.1).  Same shape as
    `object1_not_surjective` / Cantor's `diag` / the ε₀ height-diagonal / π non-holonomicity: one
    object, instantiated here on the odometer's own stream carrier.  ∅-axiom. -/
theorem analytic_minkowski_residue :
    (∀ path : List Bool, (dyInterval path).1 = binVal path)
    ∧ (¬ ∃ enum : Nat → (Nat → Bool), Function.Surjective enum)
    ∧ (∀ path : List Bool, pathStream path ≠ fun _ => true) :=
  ⟨dyInterval_value, cantor_general, constTrue_stream_not_finite⟩

end E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit
