/-!
# The status-symmetric fold forms of ℤ (canon §6.9)

`ℤ` is the difference-Lens readout (`§6.7`); its own fold is **negation** `x ↦ −x` (the directed
count-pair swap).  By `§6.9` a fold is correct only if `0` and `∞` carry the **same status** — both
genuine carrier elements, or both absent.  Plain `ℤ` has `0` (the diagonal class) but **no** `∞`:
negation's only fixed point is `0`, the `∞`-direction is an unreached limit — exactly the torsioned,
mixed-status form `§6.9` rejects.

There are precisely **two** ways to close `ℤ`'s negation fold status-symmetrically — i.e. to make `∞`
a genuine carrier element of the same status as `0`.  They are the two compactifications, and they
differ only in how the involution treats the `{0, ∞}` pair (the two admissible patterns of `§6.9`):

  - **One-point** `ℤ̂ = ℤ ∪ {∞}` with `∞ = −∞`.  Negation **fixes both** `0` and `∞` (both-fixed
    pattern).  The discrete projective line.  This is the form the *multiplicative* fold's reciprocal
    `x ↦ 1/x` reads the other way: on the projective line reciprocal **swaps** `0 ↔ ∞` and fixes the
    units `±1` (the swapped pattern), so the same one-point carrier serves both folds — additive fixes
    `{0,∞}`, multiplicative swaps it.
  - **Two-point** `ℤ̄ = ℤ ∪ {−∞, +∞}` with `+∞ ≠ −∞`.  Negation fixes `0` and **swaps** `+∞ ↔ −∞`
    (the `∞`-pair is a negation 2-cycle).  The discrete extended line.

In both, `∞` is a genuine carrier element — same status as `0` — so the torsion is cured.  And in both
the **genuine integers** `n ≠ 0` are proper negation 2-cycles `{n, −n}`: only the degenerate `0`/`∞`
sit at the fixed (or swapped-pair) loci.  So `0`/`∞` are *not* values in the sense the nonzero
integers are — they are the fold's symmetry centres, the pre-Lens residue surfacing in the carrier,
not stratum-distinguishings (`§6.5`, `§6.9`).
-/

namespace E213.Lens.Number.IntFoldForms

/-! ## Int negation helpers (∅-axiom, matched on constructors) -/

/-- `− − n = n` by constructor cases (def-reduction on `Int.neg`). -/
theorem neg_neg_int : ∀ (n : Int), - -n = n
  | Int.ofNat 0 => rfl
  | Int.ofNat (_ + 1) => rfl
  | Int.negSucc _ => rfl

/-- `n = −n ⟹ n = 0` — the negation fixed point is unique to `0` (same match as
    `Cauchy.WronskianDepth.int_ne_neg_self`). -/
theorem neg_self_zero : ∀ (n : Int), n = -n → n = 0
  | Int.ofNat 0, _ => rfl
  | Int.ofNat (_ + 1), h => Int.noConfusion h
  | Int.negSucc _, h => Int.noConfusion h

/-! ## One-point form `ℤ̂ = ℤ ∪ {∞}`, `∞ = −∞` -/

/-- `ℤ̂`: `ℤ` with a single adjoined `∞` (`none`).  The additive fold's one-point carrier. -/
abbrev IntHat := Option Int

/-- The point at infinity. -/
def IntHat.inf : IntHat := none

/-- Negation on `ℤ̂`: `∞ = −∞` (the point at infinity is negation-fixed, exactly like `0`). -/
def negHat : IntHat → IntHat
  | none => none
  | some n => some (-n)

theorem negHat_involutive : ∀ x, negHat (negHat x) = x
  | none => rfl
  | some n => congrArg some (neg_neg_int n)

/-- ★★ **One-point status-symmetry: `0` and `∞` are both negation-fixed.**  Equal status — both
    genuine carrier elements fixed by the fold. -/
theorem negHat_zero_and_inf_fixed : negHat (some 0) = some 0 ∧ negHat IntHat.inf = IntHat.inf :=
  ⟨rfl, rfl⟩

/-- ★★★ **The fixed points of the one-point fold are exactly `{0, ∞}`.**  No genuine integer is
    negation-fixed; the symmetry centres are precisely the two degeneracies. -/
theorem negHat_fixed_iff (x : IntHat) : negHat x = x ↔ x = some 0 ∨ x = none := by
  cases x with
  | none => exact ⟨fun _ => Or.inr rfl, fun _ => rfl⟩
  | some n =>
    constructor
    · intro h
      exact Or.inl (by rw [neg_self_zero n (Option.some.inj h).symm])
    · intro h
      rcases h with h0 | hnone
      · have hn : n = 0 := Option.some.inj h0
        subst hn; decide
      · exact Option.noConfusion hnone

/-- ★★ **Genuine integers are proper 2-cycles.**  For `n ≠ 0`, negation does not fix `some n`
    (`{n, −n}` is a real 2-cycle) — so the nonzero integers are values in a way `0`/`∞` are not. -/
theorem negHat_value_two_cycle (n : Int) (hn : n ≠ 0) : negHat (some n) ≠ some n := by
  intro h
  exact hn (neg_self_zero n (Option.some.inj h).symm)

/-! ## Two-point form `ℤ̄ = ℤ ∪ {−∞, +∞}`, `+∞ ≠ −∞` -/

/-- `ℤ̄`: `ℤ` with two distinct adjoined infinities.  The additive fold's two-point carrier. -/
inductive IntBar where
  | fin : Int → IntBar
  | posInf : IntBar
  | negInf : IntBar
  deriving DecidableEq

/-- Negation on `ℤ̄`: fixes `0`, **swaps** `+∞ ↔ −∞` (the `∞`-pair is a negation 2-cycle). -/
def negBar : IntBar → IntBar
  | .fin n => .fin (-n)
  | .posInf => .negInf
  | .negInf => .posInf

theorem negBar_involutive : ∀ x, negBar (negBar x) = x
  | .fin n => congrArg IntBar.fin (neg_neg_int n)
  | .posInf => rfl
  | .negInf => rfl

/-- ★★ **Two-point status-symmetry: `0` fixed, `∞` a 2-cycle.**  `+∞` and `−∞` are genuine carrier
    elements swapped by the fold — same status as `0` (in the carrier), differently patterned. -/
theorem negBar_zero_fixed_inf_swapped :
    negBar (.fin 0) = .fin 0 ∧ negBar .posInf = .negInf ∧ negBar .negInf = .posInf :=
  ⟨rfl, rfl, rfl⟩

/-- ★★★ **The only fixed point of the two-point fold is `0`.**  Both `±∞` are non-fixed (the 2-cycle),
    and no genuine nonzero integer is fixed. -/
theorem negBar_fixed_iff (x : IntBar) : negBar x = x ↔ x = .fin 0 := by
  cases x with
  | fin n =>
    constructor
    · intro h
      rw [neg_self_zero n (IntBar.fin.inj h).symm]
    · intro h
      have hn : n = 0 := IntBar.fin.inj h
      subst hn; decide
  | posInf => exact ⟨fun h => IntBar.noConfusion h, fun h => IntBar.noConfusion h⟩
  | negInf => exact ⟨fun h => IntBar.noConfusion h, fun h => IntBar.noConfusion h⟩

/-! ## The two correct fold forms, bundled -/

/-- ★★★★ **The two status-symmetric fold forms of ℤ.**  ℤ's negation fold has exactly two correct
    (torsion-free) closures, differing in the `§6.9` pattern on `{0, ∞}`:

  1. **one-point** `ℤ̂` — `0` and `∞` **both fixed** (`∞ = −∞`, the projective line; the form
     reciprocal reads by *swapping* `0 ↔ ∞`);
  2. **two-point** `ℤ̄` — `0` fixed, `∞` a **2-cycle** (`+∞ ↔ −∞`, the extended line).

In both, `∞` is a genuine carrier element of the same status as `0` (curing plain ℤ's torsion), and
the genuine integers `n ≠ 0` are proper 2-cycles `{n, −n}` — `0`/`∞` are the fold's symmetry centres,
not stratum-values. -/
theorem int_correct_fold_forms :
    -- one-point: both 0 and ∞ negation-fixed
    (negHat (some 0) = some 0 ∧ negHat IntHat.inf = IntHat.inf)
    -- two-point: 0 fixed, ∞ a negation 2-cycle
    ∧ (negBar (.fin 0) = .fin 0 ∧ negBar .posInf = .negInf ∧ negBar .negInf = .posInf)
    -- in both, the genuine integers are proper 2-cycles, never fixed
    ∧ (∀ n : Int, n ≠ 0 → negHat (some n) ≠ some n) :=
  ⟨negHat_zero_and_inf_fixed, negBar_zero_fixed_inf_swapped, negHat_value_two_cycle⟩

end E213.Lens.Number.IntFoldForms
