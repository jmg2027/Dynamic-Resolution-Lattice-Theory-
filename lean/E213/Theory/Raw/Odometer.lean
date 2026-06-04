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

end E213.Theory.Raw.Odometer
