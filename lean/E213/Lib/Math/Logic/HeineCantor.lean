import E213.Lib.Math.Logic.WKLHeineBorel

/-!
# Heine–Cantor calibrated against the fan theorem (vein-C calibration)

Classically, a pointwise-continuous function on the compact `[0,1]` is
uniformly continuous (Heine–Cantor, HC).  Constructively the compactness
HC needs is **exactly the fan theorem** — a Brouwerian/bar-induction
principle, *not* ∅-axiom.  This module pins that:

  * the ∅-axiom (constructive) direction `bar_of_pointwiseCont`:
    pointwise continuity of `f` ⟹ `Bar T` for the precision tree `T`;
  * the fan-theorem payoff `uniform_of_bounded`: `Bounded T` ⟹ a uniform
    modulus of continuity;
  * the calibration `heineCantor_of_fan`:
    `FanTheorem T → PointwiseContinuous f → UniformlyContinuous f`.

The fan theorem appears only as a **hypothesis** (`FanTheorem T`, a corpus
`Prop`), never as an axiom — so every theorem here is ∅-axiom.  This adds
HC to the reverse-math ledger at the *fan-theorem* rung, dual to
`wkl_heineBorel_calibration`'s WKL/selection-oracle rung.

## Encoding

A point of `[0,1]` is a binary stream `p : Nat → Bool`; `f` sends points
to points (output streams = dyadic values).  `takePrefix p n`
(corpus, `WKLHeineBorel`) is the length-`n` dyadic address.  "`f` pinned
to within `1/2^m` on address `s`" = `f`'s outputs on the two endpoints of
the interval `s` agree on their first `m` bits.  The tree
`T = precTree f m`: `T s = true` iff address `s` is **not yet** pinned
(still too coarse).
-/

namespace E213.Lib.Math.Logic.HeineCantor

open E213.Lib.Math.Logic
  (takePrefix takePrefix_len Bar Bounded FanTheorem length_snoc)

/-! ## §0  Address / interval primitives (all Bool/List — decidable, ∅-axiom) -/

/-- `embed s b`: the stream reading the finite address `s`, then constant
    `b` forever.  The two values `b = false / true` are the *endpoints*
    of the dyadic interval addressed by `s`. -/
def embed (s : List Bool) (b : Bool) : Nat → Bool := fun n =>
  match s.get? n with
  | some x => x
  | none   => b

/-- Prefix agreement: the length-`n` addresses of `p`, `q` coincide.
    "`p` and `q` are within `1/2^n`" in the dyadic interval metric. -/
def prefixAgree (p q : Nat → Bool) (n : Nat) : Bool :=
  takePrefix p n == takePrefix q n

/-! ## §1  The precision tree `precTree f m`

`T s = true` ("too coarse") iff the two endpoints of interval `s` are
*not* pinned to `m` bits under `f`. -/

/-- `f` is pinned to `m` bits on address `s` (Bool): the two interval
    endpoints map to outputs agreeing on their first `m` bits. -/
def pinned (f : (Nat → Bool) → (Nat → Bool)) (m : Nat) (s : List Bool) : Bool :=
  prefixAgree (f (embed s false)) (f (embed s true)) m

/-- The precision tree.  `precTree f m s = true` ⟺ address `s` is **not**
    yet pinned to `m` bits — i.e. still too coarse. -/
def precTree (f : (Nat → Bool) → (Nat → Bool)) (m : Nat) (s : List Bool) : Bool :=
  !(pinned f m s)

/-! ## §2  Continuity, in the address metric the tree speaks

`PointwiseContinuous`: at each point `p` and precision `m`, some address
depth `k` pins `f` on the interval around `p` — i.e. `precTree f m` is
`false` at the length-`k` address of `p`.  This is the modulus-as-data
form (the local depth that makes `f` vary `< 1/2^m`), matched to the
tree's own `false`-language so the calibration is exact.

`UniformlyContinuous`: one depth `k` pins `f` on *every* length-`k`
address at once — `precTree f m s = false` for all `s` of length `k`. -/

/-- **Pointwise continuity** (modulus-as-data, address metric): every
    stream `p` is eventually pinned to `m` bits. -/
def PointwiseContinuous (f : (Nat → Bool) → (Nat → Bool)) : Prop :=
  ∀ (m : Nat) (p : Nat → Bool), ∃ k, precTree f m (takePrefix p k) = false

/-- **Uniform continuity** (uniform modulus, address metric): one depth
    `k` pins every length-`k` address to `m` bits at once. -/
def UniformlyContinuous (f : (Nat → Bool) → (Nat → Bool)) : Prop :=
  ∀ m, ∃ k, ∀ s : List Bool, s.length = k → precTree f m s = false

/-! ## §3  The two ∅-axiom calibration lemmas -/

/-- ★ **Constructive direction (∅-axiom).**  Pointwise continuity makes
    the precision tree a **bar**: every infinite path (= point `p`)
    eventually leaves `precTree f m` (= is pinned to `m` bits).  This is
    `Bar (precTree f m)`, verbatim the corpus `Bar`. -/
theorem bar_of_pointwiseCont
    (f : (Nat → Bool) → (Nat → Bool)) (hpc : PointwiseContinuous f) (m : Nat) :
    Bar (precTree f m) :=
  fun p => hpc m p

/-- ★ **Fan-theorem payoff (∅-axiom).**  A uniform depth bound on the
    precision tree (`Bounded (precTree f m)`) *is* a uniform modulus: the
    bound depth `N` pins every length-`N` address to `m` bits. -/
theorem uniform_of_bounded
    (f : (Nat → Bool) → (Nat → Bool)) (m : Nat)
    (hb : Bounded (precTree f m)) :
    ∃ k, ∀ s : List Bool, s.length = k → precTree f m s = false :=
  hb

/-! ## §4  The calibration — Heine–Cantor at the fan-theorem rung -/

/-- ★★★ **Heine–Cantor, calibrated against the fan theorem (∅-axiom).**
    Given the fan theorem for the precision tree at *each* precision `m`
    (as a hypothesis, never an axiom), pointwise continuity upgrades to a
    uniform modulus.  This is HC: its classical compactness of `[0,1]` is
    here *named and measured* as the fan theorem.

    Per-`m` fan hypothesis: `∀ m, FanTheorem (precTree f m)`.  The
    constructive content `bar_of_pointwiseCont` feeds each `FanTheorem`;
    its output `Bounded` is unpacked by `uniform_of_bounded` into the
    uniform depth. -/
theorem heineCantor_of_fan
    (f : (Nat → Bool) → (Nat → Bool))
    (hfan : ∀ m, FanTheorem (precTree f m)) :
    PointwiseContinuous f → UniformlyContinuous f :=
  fun hpc m =>
    uniform_of_bounded f m (hfan m (bar_of_pointwiseCont f hpc m))

/-- ★★★ **Bundled calibration** — the ledger entry.  Both ∅-axiom halves
    (constructive bar; bounded ⟹ uniform modulus) plus the fan-conditional
    HC implication, mirroring `wkl_heineBorel_calibration`'s shape. -/
theorem heineCantor_calibration
    (f : (Nat → Bool) → (Nat → Bool)) :
    (PointwiseContinuous f → ∀ m, Bar (precTree f m))
    ∧ (∀ m, Bounded (precTree f m) →
        ∃ k, ∀ s : List Bool, s.length = k → precTree f m s = false)
    ∧ ((∀ m, FanTheorem (precTree f m)) →
        PointwiseContinuous f → UniformlyContinuous f) :=
  ⟨fun hpc m => bar_of_pointwiseCont f hpc m,
   fun m hb => uniform_of_bounded f m hb,
   fun hfan => heineCantor_of_fan f hfan⟩

end E213.Lib.Math.Logic.HeineCantor
