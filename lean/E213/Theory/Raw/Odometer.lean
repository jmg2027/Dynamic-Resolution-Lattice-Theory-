import E213.Theory.Raw.CoResidue

/-!
# Theory.Raw.Odometer — the `+1` adding machine on bit-streams; the carry is the residue unit

The shift (`CoResidue` §19) is one of the two fundamental maps on the bit-stream space
`Nat → Bool`; the other is the **odometer** — the `+1` adding machine (least-significant-bit-first
binary increment with carry).  This file builds it ∅-axiom and reads its carry as the residue
unit, so the µF/νF mirror appears at the arithmetic-odometer scale:

  * the carry starts at the unit (`carry f 0 = true`, the `+1`) and survives into position `n+1`
    only through a `1` at `n` — it propagates through the *leading run of 1s*;
  * the carry **terminates iff the stream has a floor** (a `false` / `0`),
    `carry_dies_iff_has_false`.  A stream with a floor resolves the `+1` locally — the µF face
    (the descent terminating at an atom, `Lambek.terminal_iff_atom`); the **all-`true`** stream
    has the carry running *forever* (`allTrue_carry_forever`) — the `+1` escaping to a new rung,
    the νF face (`MuNuMirror.ascent_unbounded`);
  * and the all-`true` stream is exactly the seed of the canonical νF escape `spineL`
    (`CoResidue.spineL_eq_boolSpine_true`): so the residue escape *is* the odometer overflow —
    the `+1` that never lands wraps the 2-adic `…111` to `…000` (`odo_allTrue`).

The mathematics is the 2-adic odometer (a known object — the adding machine / Vershik–Bratteli
`+1`); the 213 reading is that its `+1` IS the self-pointing act, its carry IS the residue unit
(`Lens/Number/SharedUnitAcrossReadings`), and its non-terminating overflow IS the νF escape.
All ∅-axiom, pointwise (Bool computation + finite induction; no `funext`).
-/

namespace E213.Theory.Raw.Odometer

open E213.Theory.Raw.CoResidue (spineL boolSpine spineL_eq_boolSpine_true)

/-- The carry of the `+1` adding machine (LSB-first): it starts at the unit `true` (the `+1`)
    and survives into position `n+1` only through a `1` at position `n`. -/
def carry (f : Nat → Bool) : Nat → Bool
  | 0     => true
  | n + 1 => carry f n && f n

/-- The `+1` adding machine (binary increment): output bit = input `xor` carry. -/
def odo (f : Nat → Bool) : Nat → Bool := fun n => Bool.xor (f n) (carry f n)

/-- The carry starts at the residue unit `1`. -/
theorem carry_zero (f : Nat → Bool) : carry f 0 = true := rfl

/-- The carry survives a step only through a `1` (equation lemma for `carry`). -/
theorem carry_succ (f : Nat → Bool) (n : Nat) : carry f (n + 1) = (carry f n && f n) := rfl

/-- The odometer output bit (equation lemma for `odo`). -/
theorem odo_apply (f : Nat → Bool) (n : Nat) : odo f n = Bool.xor (f n) (carry f n) := rfl

/-- ★★ **A dead carry exposes a floor.**  If the carry is `false` at some position `N`, the
    stream has a `false` (a floor / `0`) at some earlier position — extracted by induction down
    the carry chain (`carry f (n+1) = carry f n && f n`). -/
theorem has_false_of_carry_false (f : Nat → Bool) :
    ∀ N, carry f N = false → ∃ k, f k = false
  | 0     => fun h => by rw [carry_zero] at h; exact Bool.noConfusion h
  | N + 1 => fun h => by
      rw [carry_succ] at h
      cases hfn : f N with
      | false => exact ⟨N, hfn⟩
      | true  =>
          rw [hfn, Bool.and_true] at h
          exact has_false_of_carry_false f N h

/-- ★★ **The carry runs forever on the all-`true` stream.**  No floor (`∀ n, f n = true`) ⟹ the
    `+1` never resolves: `carry f n = true` for every `n` — the νF face of the odometer. -/
theorem allTrue_carry_forever (f : Nat → Bool) (h : ∀ n, f n = true) :
    ∀ n, carry f n = true
  | 0     => carry_zero f
  | n + 1 => by rw [carry_succ, allTrue_carry_forever f h n, Bool.true_and, h n]

/-- ★★★ **The carry terminates iff the stream has a floor.**  `(∃ N, carry f N = false) ↔
    (∃ k, f k = false)`: the `+1` resolves in finitely many steps exactly when the stream has a
    `false` (a `0` to absorb the carry).  Forward by `has_false_of_carry_false`; backward, a
    `false` at `k` kills the carry one step later (`carry f (k+1) = carry f k && false = false`).
    This is the µF/νF dichotomy at the odometer scale — terminate-with-floor vs escape-without. -/
theorem carry_dies_iff_has_false (f : Nat → Bool) :
    (∃ N, carry f N = false) ↔ (∃ k, f k = false) := by
  constructor
  · rintro ⟨N, hN⟩
    exact has_false_of_carry_false f N hN
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [carry_succ, hk, Bool.and_false]⟩

/-- ★★ **The all-`true` stream incremented wraps to all-`false`** (the 2-adic `…111 + 1 = …000`,
    i.e. `(−1) + 1 = 0`): every output bit is `Bool.xor true true = false`, since the carry never
    dies (`allTrue_carry_forever`).  The overflow has nowhere to land. -/
theorem odo_allTrue (n : Nat) : odo (fun _ => true) n = false := by
  rw [odo_apply, allTrue_carry_forever (fun _ => true) (fun _ => rfl) n]
  decide

/-- ★★★ **The canonical νF escape is the odometer overflow.**  The seed of `spineL`
    (`= boolSpine (fun _ => true)`, `CoResidue.spineL_eq_boolSpine_true`) is the all-`true`
    stream — exactly the stream whose `+1`-carry never terminates (`allTrue_carry_forever`), so
    the `+1` wraps with nowhere to land (`odo_allTrue`).  The residue's canonical escape, read
    arithmetically, *is* the odometer's non-terminating overflow: "the escape" (νF) and "the
    carry that never lands" (the `+1` demanding a new rung) are one object. -/
theorem spineL_seed_is_odo_overflow :
    (∀ q, spineL q = boolSpine (fun _ => true) q)
    ∧ (∀ n, carry (fun _ => true) n = true)
    ∧ (∀ n, odo (fun _ => true) n = false) :=
  ⟨spineL_eq_boolSpine_true,
   allTrue_carry_forever (fun _ => true) (fun _ => rfl),
   odo_allTrue⟩

/-- ★★★ **The µF/νF mirror at the odometer scale.**  The `+1` adding machine's carry: starts at
    the residue unit (`carry f 0 = true`); terminates iff the stream has a floor
    (`carry_dies_iff_has_false` — the µF face, the `+1` resolving locally); and runs forever on
    the all-`true` stream (`allTrue_carry_forever` — the νF face, the `+1` escaping, the seed of
    `spineL` per `spineL_seed_is_odo_overflow`).  So `Lambek.terminal_iff_atom` /
    `MuNuMirror.ascent_unbounded` reappear as a property of the odometer carry, with the carry the
    one residue unit `+1`.  ∅-axiom. -/
theorem odometer_mu_nu_mirror (f : Nat → Bool) :
    carry f 0 = true
    ∧ ((∃ N, carry f N = false) ↔ (∃ k, f k = false))
    ∧ ((∀ n, f n = true) → ∀ n, carry f n = true) :=
  ⟨carry_zero f, carry_dies_iff_has_false f, allTrue_carry_forever f⟩

/-! ## §2 — the successor dynamics: the `+1` is injective and interlocks with the descent

The two fundamental maps on the bit-streams are the **descent** (the shift `σ`, drop the
least-significant bit — the µF face, `CoResidue` §19) and the **ascent unit** (the odometer `+1`,
the νF face).  This section shows how they interlock, and that the `+1` is the residue's
*injective* successor:

  * **the carry recursion** — `carry f (n+1) = f 0 && carry (shift f) n` (`carry_shift`): the
    carry passes position `0` only through the low bit, so it is the low bit *conjoined* with the
    shifted carry;
  * **the descent–increment skew** — `σ (odo f) = odo (σ f)` gated by the low bit
    (`shift_odo`): dropping the low bit after incrementing equals incrementing the tail *iff* the
    low bit was `1` (the carry propagated), else it is just the descent — the adding-machine
    recursion, the precise way the `+1` and the descent commute;
  * **the `+1` never collides** — `odo` is *injective* (`odo_injective`): the residue's
    successor never sends two streams to one, the odometer-scale form of `tower_no_cycle` /
    no-exterior (`MuNuMirror`: the ascent never returns).

All ∅-axiom, pointwise (Bool computation + finite induction). -/

/-- The descent: drop the least-significant bit (the shift `σ`). -/
def shift (f : Nat → Bool) : Nat → Bool := fun n => f (n + 1)

/-- `shift` output (equation lemma): `shift f n = f (n+1)`. -/
theorem shift_apply (f : Nat → Bool) (n : Nat) : shift f n = f (n + 1) := rfl

/-- ★★ **The carry recursion.**  `carry f (n+1) = f 0 && carry (shift f) n`: the carry reaches
    position `n+1` only by passing the low bit `f 0` *and* the carry of the shifted stream — the
    leading run of `1`s, split off one bit at a time. -/
theorem carry_shift (f : Nat → Bool) :
    ∀ n, carry f (n + 1) = (f 0 && carry (shift f) n)
  | 0     => by rw [carry_succ, carry_zero, Bool.true_and, carry_zero, Bool.and_true]
  | n + 1 => by
      rw [carry_succ, carry_shift f n, carry_succ, Bool.and_assoc, shift_apply]

/-- ★★★ **The descent–increment skew relation.**  `shift (odo f) n = (shift f n) xor (f 0 &&
    carry (shift f) n)`: descending after the `+1` is the descent value corrected by the carry,
    which passes only through the low bit.  Reading the cases: when `f 0 = true` the right factor
    is `carry (shift f) n`, so `shift (odo f) = odo (shift f)` (the `+1` propagated to the tail);
    when `f 0 = false` it is `false`, so `shift (odo f) = shift f` (the `+1` stopped at bit 0).
    The adding-machine recursion — how the descent (µF) and the ascent unit (νF) commute. -/
theorem shift_odo (f : Nat → Bool) (n : Nat) :
    shift (odo f) n = Bool.xor (shift f n) (f 0 && carry (shift f) n) := by
  show odo f (n + 1) = Bool.xor (f (n + 1)) (f 0 && carry (shift f) n)
  rw [odo_apply, carry_shift f n]

/-- The carry depends only on the bits below: agreement on `[0, n)` forces equal carries. -/
theorem carry_congr {f g : Nat → Bool} :
    ∀ n, (∀ m, m < n → f m = g m) → carry f n = carry g n
  | 0     => fun _ => by rw [carry_zero, carry_zero]
  | n + 1 => fun h => by
      rw [carry_succ, carry_succ,
          carry_congr n (fun m hm => h m (Nat.lt_succ_of_lt hm)), h n (Nat.lt_succ_self n)]

/-- `xor` cancels on the right: `a xor c = b xor c → a = b` (Bool). -/
theorem xor_right_cancel {a b c : Bool} (h : Bool.xor a c = Bool.xor b c) : a = b := by
  cases a <;> cases b <;> cases c <;> first | rfl | exact absurd h (by decide)

/-- ★★★ **The residue's successor is injective.**  `odo f = odo g` (pointwise) ⟹ `f = g`: the
    `+1` adding machine never sends two distinct streams to one.  By induction on the bit
    position — the output bit `odo f n = f n xor carry f n`, the carry fixed by the lower bits
    (`carry_congr`), so `xor`-cancellation (`xor_right_cancel`) recovers `f n = g n`.  This is the
    odometer-scale `tower_no_cycle` (`MuNuMirror`): the act of adding the unit never returns, the
    no-exterior signature read on the `+1`. -/
theorem odo_injective {f g : Nat → Bool} (h : ∀ n, odo f n = odo g n) : ∀ n, f n = g n := by
  have agree : ∀ n, ∀ m, m < n → f m = g m := by
    intro n
    induction n with
    | zero => intro m hm; exact absurd hm (Nat.not_lt_zero m)
    | succ n ih =>
        intro m hm
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hlt | heq
        · exact ih m hlt
        · subst heq
          have hc : carry f m = carry g m := carry_congr m ih
          have he : odo f m = odo g m := h m
          rw [odo_apply, odo_apply, hc] at he
          exact xor_right_cancel he
  intro n
  exact agree (n + 1) n (Nat.lt_succ_self n)

/-- ★★★ **The residue's successor dynamics, bundled.**  The `+1` adding machine on the residue's
    bit-streams is an **injective** map (`odo_injective` — never returns, no-exterior at the
    odometer scale) whose interaction with the descent is the adding-machine recursion
    (`shift_odo` — the `+1` and the shift commute through the carry, gated by the low bit), the
    carry itself splitting one bit at a time (`carry_shift`).  Together with §1 (the carry
    terminates iff there is a floor; the canonical escape is the overflow), this makes the
    odometer the residue's complete successor structure: the ascent unit `+1` as an injective
    dynamical system interlocking with the µF descent.  ∅-axiom. -/
theorem successor_dynamics :
    (∀ (f : Nat → Bool) n, carry f (n + 1) = (f 0 && carry (shift f) n))
    ∧ (∀ (f : Nat → Bool) n, shift (odo f) n = Bool.xor (shift f n) (f 0 && carry (shift f) n))
    ∧ (∀ {f g : Nat → Bool}, (∀ n, odo f n = odo g n) → ∀ n, f n = g n) :=
  ⟨carry_shift, shift_odo, odo_injective⟩

end E213.Theory.Raw.Odometer
