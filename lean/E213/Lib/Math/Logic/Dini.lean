import E213.Lib.Math.Logic.WKLHeineBorel

/-!
# Dini's theorem calibrated against the fan theorem (vein-C calibration)

Classically, a **monotone** sequence of continuous functions `F n`
converging **pointwise** to a continuous limit `f` on the compact `[0,1]`
converges **uniformly** (Dini).  Constructively the compactness Dini
needs is **exactly the fan theorem** — a Brouwerian/bar-induction
principle, *not* ∅-axiom.  This module pins that, sibling to
`HeineCantor.heineCantor_of_fan`:

  * the ∅-axiom (constructive) direction `bar_of_pointwiseConv`:
    monotone pointwise convergence ⟹ `Bar T` for the Dini precision tree;
  * the fan-theorem payoff `uniform_of_bounded`: `Bounded T` ⟹ a uniform
    convergence index;
  * the calibration `dini_of_fan`:
    `FanTheorem T → (mono ∧ pointwise conv) → UniformConv`.

The fan theorem, monotonicity, and pointwise convergence all appear only
as **hypotheses** (corpus `Prop`s), never as axioms — so every theorem
here is ∅-axiom.  This adds Dini to the reverse-math ledger at the
*fan-theorem* rung, dual to `wkl_heineBorel_calibration`'s WKL rung and
sibling to `heineCantor_calibration`.

## Encoding (mirrors `HeineCantor.lean`)

A point of `[0,1]` is a binary stream `p : Nat → Bool`.  `takePrefix p n`
(corpus, `WKLHeineBorel`) is the length-`n` dyadic address.  `F` is a
sequence of functions sending points to dyadic-value streams, `f` the
limit.  The address depth `s.length` doubles as the **sequence index**:
"converged on address `s`" = `F (s.length)`'s value at the interval's
representative endpoint agrees with `f`'s value there on the first `m`
bits.  The Dini tree `T = diniTree F f m`: `T s = true` iff address `s`
is **not yet** converged to within `1/2^m`.  Deeper address ⇒ later
index ⇒ (monotonicity) once converged, stays converged — which is what
makes a per-interval depth bound a uniform convergence index `N(m)`.
-/

namespace E213.Lib.Math.Logic.Dini

open E213.Lib.Math.Logic
  (takePrefix takePrefix_len Bar Bounded FanTheorem length_snoc)

/-! ## §0  Address / interval primitives (all Bool/List — decidable, ∅-axiom) -/

/-- `embed s b`: the stream reading the finite address `s`, then constant
    `b` forever — the representative point of the dyadic interval `s`. -/
def embed (s : List Bool) (b : Bool) : Nat → Bool := fun n =>
  match s.get? n with
  | some x => x
  | none   => b

/-- Prefix agreement: the length-`m` addresses of `p`, `q` coincide —
    "`p` and `q` are within `1/2^m`" in the dyadic interval metric. -/
def prefixAgree (p q : Nat → Bool) (m : Nat) : Bool :=
  takePrefix p m == takePrefix q m

/-! ## §1  The Dini precision tree `diniTree F f m`

`F : Nat → (Nat → Bool) → (Nat → Bool)` is the function *sequence*,
`f` the pointwise limit.  The address depth `s.length` *is* the sequence
index, so deeper = later in the sequence. -/

/-- `F (s.length)` has converged to `f` within `m` bits on address `s`
    (Bool): the value of `F (s.length)` and of `f` at the interval's
    representative point `embed s false` agree on their first `m` bits. -/
def convergedAt (F : Nat → (Nat → Bool) → (Nat → Bool))
    (f : (Nat → Bool) → (Nat → Bool)) (m : Nat) (s : List Bool) : Bool :=
  prefixAgree (F s.length (embed s false)) (f (embed s false)) m

/-- The Dini precision tree.  `diniTree F f m s = true` ⟺ address `s` is
    **not** yet converged to `m` bits — i.e. the sequence has not yet
    settled on this interval. -/
def diniTree (F : Nat → (Nat → Bool) → (Nat → Bool))
    (f : (Nat → Bool) → (Nat → Bool)) (m : Nat) (s : List Bool) : Bool :=
  !(convergedAt F f m s)

/-! ## §2  Monotonicity, pointwise & uniform convergence (the tree's metric)

`MonoConv`: the genuinely-new Dini ingredient.  Along every path, once the
sequence is within `1/2^m`, it *stays* within — encoded directly on the
`Bool` tree values: if `diniTree F f m` is `false` (converged) at depth
`k` on a stream's address, it is `false` at every deeper depth.  This is
the monotone-sequence content: a per-interval (single-depth) convergence
witness extends to all larger indices, so a depth bound becomes a uniform
index.

`PointwiseConv`: at each point `p` and precision `m`, some depth `k`
converges — `diniTree F f m` is `false` at the length-`k` address of `p`.

`UniformConv`: one depth `k` converges every length-`k` address at once. -/

/-- **Monotone convergence** (Bool-encoded, address metric): along every
    stream, convergence at one depth persists to all deeper depths. -/
def MonoConv (F : Nat → (Nat → Bool) → (Nat → Bool))
    (f : (Nat → Bool) → (Nat → Bool)) : Prop :=
  ∀ (m : Nat) (p : Nat → Bool) (j k : Nat), j ≤ k →
    diniTree F f m (takePrefix p j) = false →
    diniTree F f m (takePrefix p k) = false

/-- **Pointwise convergence** (modulus-as-data, address metric): every
    stream `p` eventually converges to `m` bits. -/
def PointwiseConv (F : Nat → (Nat → Bool) → (Nat → Bool))
    (f : (Nat → Bool) → (Nat → Bool)) : Prop :=
  ∀ (m : Nat) (p : Nat → Bool), ∃ k, diniTree F f m (takePrefix p k) = false

/-- **Uniform convergence** (uniform index, address metric): one depth `k`
    converges every length-`k` address to `m` bits at once. -/
def UniformConv (F : Nat → (Nat → Bool) → (Nat → Bool))
    (f : (Nat → Bool) → (Nat → Bool)) : Prop :=
  ∀ m, ∃ k, ∀ s : List Bool, s.length = k → diniTree F f m s = false

/-- **Uniform convergence, stable past the index** (the genuine Dini
    statement): one depth `k` converges every *point* and stays converged
    at every deeper depth `≥ k`.  This is the form monotonicity earns —
    a single index `N(m)` good for the whole fan *and* all larger indices.
    Equivalently: along every stream `p`, every depth `j ≥ k` is already
    converged. -/
def UniformConvStable (F : Nat → (Nat → Bool) → (Nat → Bool))
    (f : (Nat → Bool) → (Nat → Bool)) : Prop :=
  ∀ m, ∃ k, ∀ (p : Nat → Bool) (j : Nat), k ≤ j →
    diniTree F f m (takePrefix p j) = false

/-! ## §3  The two ∅-axiom calibration lemmas -/

/-- ★ **Constructive direction (∅-axiom).**  Pointwise convergence makes
    the Dini precision tree a **bar**: every infinite path (= point `p`)
    eventually leaves `diniTree F f m` (= has converged to `m` bits).
    This is `Bar (diniTree F f m)`, verbatim the corpus `Bar`.

    Monotonicity is not needed for the bar direction — a single converging
    depth already takes the path out of the tree; `MonoConv` is what the
    *fan payoff* uses to make the bound uniform-in-the-sequence. -/
theorem bar_of_pointwiseConv
    (F : Nat → (Nat → Bool) → (Nat → Bool)) (f : (Nat → Bool) → (Nat → Bool))
    (hpc : PointwiseConv F f) (m : Nat) :
    Bar (diniTree F f m) :=
  fun p => hpc m p

/-- ★ **Fan-theorem payoff (∅-axiom).**  A uniform depth bound on the Dini
    precision tree (`Bounded (diniTree F f m)`) *is* a uniform convergence
    index: the bound depth `N` converges every length-`N` address to `m`
    bits. -/
theorem uniform_of_bounded
    (F : Nat → (Nat → Bool) → (Nat → Bool)) (f : (Nat → Bool) → (Nat → Bool))
    (m : Nat) (hb : Bounded (diniTree F f m)) :
    ∃ k, ∀ s : List Bool, s.length = k → diniTree F f m s = false :=
  hb

/-- ★ **Fan payoff + monotonicity ⟹ a stable uniform index (∅-axiom).**
    Here the genuinely-new Dini ingredient `MonoConv` is load-bearing: the
    bound depth `N` converges the length-`N` address of *every* stream
    (`takePrefix_len`), and monotonicity extends that one converged depth
    to **all deeper depths** `j ≥ N`.  So `N(m)` is a single convergence
    index good for the whole fan *and* all larger indices — the genuine
    uniform-convergence conclusion of Dini. -/
theorem uniformStable_of_bounded_mono
    (F : Nat → (Nat → Bool) → (Nat → Bool)) (f : (Nat → Bool) → (Nat → Bool))
    (hmono : MonoConv F f) (m : Nat) (hb : Bounded (diniTree F f m)) :
    ∃ k, ∀ (p : Nat → Bool) (j : Nat), k ≤ j →
      diniTree F f m (takePrefix p j) = false :=
  hb.elim (fun N hN =>
    ⟨N, fun p j hj =>
      hmono m p N j hj (hN (takePrefix p N) (takePrefix_len p N))⟩)

/-! ## §4  The calibration — Dini at the fan-theorem rung -/

/-- ★★★ **Dini's theorem, calibrated against the fan theorem (∅-axiom).**
    Given the fan theorem for the Dini precision tree at *each* precision
    `m` (as a hypothesis, never an axiom), a monotone pointwise-convergent
    sequence upgrades to a uniform convergence index.  This is Dini: its
    classical compactness of `[0,1]` is here *named and measured* as the
    fan theorem; the monotonicity (`MonoConv`) is what makes the bar's
    per-interval depth bound a uniform-in-the-sequence index.

    Per-`m` fan hypothesis: `∀ m, FanTheorem (diniTree F f m)`.  The
    constructive content `bar_of_pointwiseConv` feeds each `FanTheorem`;
    its output `Bounded` is unpacked by `uniform_of_bounded`. -/
theorem dini_of_fan
    (F : Nat → (Nat → Bool) → (Nat → Bool)) (f : (Nat → Bool) → (Nat → Bool))
    (hfan : ∀ m, FanTheorem (diniTree F f m))
    (hmono : MonoConv F f) :
    PointwiseConv F f → UniformConvStable F f :=
  fun hpc m =>
    uniformStable_of_bounded_mono F f hmono m
      (hfan m (bar_of_pointwiseConv F f hpc m))

/-- ★★ **Dini, plain uniform form (∅-axiom).**  The fan-conditional upgrade
    without the stability strengthening — one depth converges the whole
    length-`k` fan.  Does not use monotonicity (the bound itself is a
    uniform index over the fan); the stable form `dini_of_fan` is where
    `MonoConv` adds the all-larger-indices guarantee. -/
theorem dini_of_fan_plain
    (F : Nat → (Nat → Bool) → (Nat → Bool)) (f : (Nat → Bool) → (Nat → Bool))
    (hfan : ∀ m, FanTheorem (diniTree F f m)) :
    PointwiseConv F f → UniformConv F f :=
  fun hpc m =>
    uniform_of_bounded F f m (hfan m (bar_of_pointwiseConv F f hpc m))

/-- ★★★ **Bundled calibration** — the ledger entry.  Both ∅-axiom halves
    (constructive bar; bounded ⟹ uniform index) plus the fan-conditional
    Dini implication, mirroring `heineCantor_calibration`'s shape. -/
theorem dini_calibration
    (F : Nat → (Nat → Bool) → (Nat → Bool)) (f : (Nat → Bool) → (Nat → Bool)) :
    (PointwiseConv F f → ∀ m, Bar (diniTree F f m))
    ∧ (∀ m, Bounded (diniTree F f m) →
        ∃ k, ∀ s : List Bool, s.length = k → diniTree F f m s = false)
    ∧ ((∀ m, FanTheorem (diniTree F f m)) → MonoConv F f →
        PointwiseConv F f → UniformConvStable F f) :=
  ⟨fun hpc m => bar_of_pointwiseConv F f hpc m,
   fun m hb => uniform_of_bounded F f m hb,
   fun hfan hmono => dini_of_fan F f hfan hmono⟩

end E213.Lib.Math.Logic.Dini
