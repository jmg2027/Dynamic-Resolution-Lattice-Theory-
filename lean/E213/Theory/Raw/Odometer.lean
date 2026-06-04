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

/-! ## §3 — the predecessor `−1`: the residue unit generates a `ℤ`-action (the `+1` is invertible)

The odometer is the residue's `+1`; its inverse is the `−1` adding machine — the **predecessor**,
which *borrows* instead of carrying.  The borrow starts at the unit and propagates through the
leading `0`s (subtracting `1` from `…0` borrows past every `0`), dual to the carry propagating
through the leading `1`s.  The two are mutually inverse (`dec_odo`, `odo_dec`), so the `+1` is a
**bijection** of the residue's bit-stream space, with the `−1` its inverse — the residue unit,
read as the difference-Lens generator (`theory/essays/analysis/integers_as_difference_lens.md`),
generates a `ℤ`-action `(±1)` on the escape space.  Injective (§2) + invertible here: the unit's
action is free of collapse, the no-exterior signature made a group action.  All ∅-axiom. -/

/-- The borrow of the `−1` adding machine (LSB-first): starts at the unit `true` and survives
    into position `n+1` only through a `0` at `n` — dual to `carry` (which survives through `1`). -/
def borrow (f : Nat → Bool) : Nat → Bool
  | 0     => true
  | n + 1 => borrow f n && Bool.not (f n)

/-- The `−1` adding machine (binary decrement): output bit = input `xor` borrow. -/
def dec (f : Nat → Bool) : Nat → Bool := fun n => Bool.xor (f n) (borrow f n)

/-- The borrow survives a step only through a `0` (equation lemma for `borrow`). -/
theorem borrow_succ (f : Nat → Bool) (n : Nat) :
    borrow f (n + 1) = (borrow f n && Bool.not (f n)) := rfl

/-- The decrement output bit (equation lemma for `dec`). -/
theorem dec_apply (f : Nat → Bool) (n : Nat) : dec f n = Bool.xor (f n) (borrow f n) := rfl

/-- Bool identity: `b && not (xor a b) = b && a` (the carry/borrow cancellation, `+` side). -/
theorem and_not_xor (a b : Bool) : (b && Bool.not (Bool.xor a b)) = (b && a) := by
  cases a <;> cases b <;> decide

/-- Bool identity: `b && xor a b = b && not a` (the carry/borrow cancellation, `−` side). -/
theorem and_xor (a b : Bool) : (b && Bool.xor a b) = (b && Bool.not a) := by
  cases a <;> cases b <;> decide

/-- Bool identity: `xor (xor a b) b = a` (`xor` is its own inverse on the right). -/
theorem xor_cancel (a b : Bool) : Bool.xor (Bool.xor a b) b = a := by
  cases a <;> cases b <;> decide

/-- ★★ **The borrow of the successor is the carry.**  `borrow (odo f) n = carry f n`: subtracting
    `1` from `f + 1` borrows exactly where adding `1` to `f` carried — the two propagations are
    the same leading run, read with opposite digits. -/
theorem borrow_odo (f : Nat → Bool) : ∀ n, borrow (odo f) n = carry f n
  | 0     => rfl
  | n + 1 => by rw [borrow_succ, borrow_odo f n, odo_apply, carry_succ, and_not_xor]

/-- ★★ **The carry of the predecessor is the borrow** (dual of `borrow_odo`). -/
theorem carry_dec (f : Nat → Bool) : ∀ n, carry (dec f) n = borrow f n
  | 0     => rfl
  | n + 1 => by rw [carry_succ, carry_dec f n, dec_apply, borrow_succ, and_xor]

/-- ★★★ **The predecessor undoes the successor.**  `dec (odo f) = f` pointwise: `(f + 1) − 1 = f`.
    The output is `(f n xor carry f n) xor carry f n = f n` (`xor_cancel`), once the borrow of the
    successor is identified with its carry (`borrow_odo`). -/
theorem dec_odo (f : Nat → Bool) (n : Nat) : dec (odo f) n = f n := by
  rw [dec_apply, borrow_odo f n, odo_apply, xor_cancel]

/-- ★★★ **The successor undoes the predecessor.**  `odo (dec f) = f` pointwise: `(f − 1) + 1 = f`
    (dual of `dec_odo`, via `carry_dec`). -/
theorem odo_dec (f : Nat → Bool) (n : Nat) : odo (dec f) n = f n := by
  rw [odo_apply, carry_dec f n, dec_apply, xor_cancel]

/-- ★★★ **The residue unit generates a `ℤ`-action: the `+1` is a bijection.**  The odometer `odo`
    (`+1`) and the predecessor `dec` (`−1`) are mutually inverse (`dec_odo`, `odo_dec`) and `odo`
    is injective (§2) — so the residue unit acts *invertibly* on the bit-stream escape space, the
    `+1` and `−1` the difference-Lens generators
    (`theory/essays/analysis/integers_as_difference_lens.md`) of a `ℤ`-action.  The act of adding
    the unit never collapses and is always undoable: the no-exterior / never-return signature
    (`MuNuMirror.tower_no_cycle`) made a group action on the residue's escapes.  ∅-axiom. -/
theorem odo_unit_action :
    (∀ (f : Nat → Bool) n, dec (odo f) n = f n)
    ∧ (∀ (f : Nat → Bool) n, odo (dec f) n = f n)
    ∧ (∀ {f g : Nat → Bool}, (∀ n, odo f n = odo g n) → ∀ n, f n = g n) :=
  ⟨dec_odo, odo_dec, odo_injective⟩

/-! ## §4 — the µF/νF reversibility asymmetry: descent forgets, the ascent unit remembers

The two fundamental maps differ sharply in *reversibility*.  The **descent** (shift `σ`) is
**surjective but not injective** — it is a forgetful quotient: every stream is some stream's tail
(`shift_surjective`), but distinct streams that agree from position `1` on collapse to the same
tail (`shift_not_injective`), the dropped least-significant bit being lost.  The **ascent unit**
(odometer `+1`) is **bijective** (§2 injective + §3 invertible): it loses nothing and is always
undoable.

So the µF face grounds *irreversibly* (descent discards information, bottoming out at an atom —
`Lambek.terminal_iff_atom`), while the νF ascent unit escapes *reversibly* (the `+1` is a `ℤ`-action,
`odo_unit_action`).  Reversibility is the operational signature of the asymmetry: grounding forgets,
the unit remembers.  All ∅-axiom. -/

/-- Prepend a bit: `cons b f` is `b` at position `0` and `f` shifted up after. -/
def cons (b : Bool) (f : Nat → Bool) : Nat → Bool
  | 0     => b
  | n + 1 => f n

/-- The descent undoes a prepend: `shift (cons b f) = f` (the dropped bit is `b`). -/
theorem shift_cons (b : Bool) (f : Nat → Bool) (n : Nat) : shift (cons b f) n = f n := rfl

/-- ★★ **The descent is surjective.**  Every stream is some stream's tail: `shift (cons false f) =
    f`.  The descent reaches everything — it is onto. -/
theorem shift_surjective (f : Nat → Bool) : ∃ g : Nat → Bool, ∀ n, shift g n = f n :=
  ⟨cons false f, shift_cons false f⟩

/-- ★★ **The descent is not injective (it forgets).**  Two streams agreeing from position `1` on
    but differing at position `0` (`cons true c` vs `cons false c`) have the *same* tail under the
    shift — the dropped least-significant bit is lost.  So the descent is a forgetful quotient,
    not reversible. -/
theorem shift_not_injective :
    ∃ f g : Nat → Bool, (∀ n, shift f n = shift g n) ∧ (∃ m, f m ≠ g m) :=
  ⟨cons true (fun _ => false), cons false (fun _ => false),
   fun n => by rw [shift_cons, shift_cons], ⟨0, by decide⟩⟩

/-- ★★★ **The reversibility asymmetry: descent forgets, the ascent unit remembers.**  The descent
    (shift) is **surjective** (`shift_surjective`) but **not injective** (`shift_not_injective`) —
    a forgetful quotient, the µF face that grounds by discarding the low bit.  The ascent unit
    (odometer `+1`) is **bijective** — injective (`odo_injective`) and invertible
    (`dec_odo`) — the νF face that escapes reversibly, the residue unit's `ℤ`-action losing
    nothing.  Reversibility distinguishes the two faces: µF grounds irreversibly, νF's unit is a
    group action.  ∅-axiom. -/
theorem descent_forgets_ascent_remembers :
    (∀ f : Nat → Bool, ∃ g, ∀ n, shift g n = f n)
    ∧ (∃ f g : Nat → Bool, (∀ n, shift f n = shift g n) ∧ (∃ m, f m ≠ g m))
    ∧ (∀ {f g : Nat → Bool}, (∀ n, odo f n = odo g n) → ∀ n, f n = g n)
    ∧ (∀ (f : Nat → Bool) n, dec (odo f) n = f n) :=
  ⟨shift_surjective, shift_not_injective, odo_injective, dec_odo⟩

/-! ## §5 — the odometer is the `ℤ₂`-successor homeomorphism (bijective + continuous)

The bit-stream space `Nat → Bool` is the residue's escape carrier; under the product (Cantor)
topology it is the `2`-adic integers `ℤ₂ = lim ℤ/2ᵏ`.  The odometer is the `+1` on it, and it is a
**homeomorphism**: bijective (§3, `dec` the inverse) and **continuous** — each output bit `n`
depends only on the input bits `≤ n` (`odo_prefix_determined`), the carry reaching no further than
it has seen.  So the residue's `+1` is the `ℤ₂`-successor as a topological group automorphism: the
escape space carries the `2`-adic integer structure, generated by the residue unit.  ∅-axiom. -/

/-- ★★★ **The odometer is continuous (prefix-determined).**  `odo f n` depends only on the input
    bits at positions `≤ n`: if `f` and `g` agree on `[0, n]` then `odo f n = odo g n` — the carry
    reaches no further than the bits it has passed (`carry_congr`).  This is continuity in the
    Cantor topology, making `odo` a well-defined map on `ℤ₂ = lim ℤ/2ᵏ`. -/
theorem odo_prefix_determined {f g : Nat → Bool} (n : Nat)
    (h : ∀ m, m ≤ n → f m = g m) : odo f n = odo g n := by
  rw [odo_apply, odo_apply, carry_congr n (fun m hm => h m (Nat.le_of_lt hm)),
      h n (Nat.le_refl n)]

/-- ★★★ **The odometer is the `ℤ₂`-successor homeomorphism.**  On the residue's bit-stream escape
    space (the `2`-adic integers under the Cantor topology), the `+1` is a homeomorphism: bijective
    (`dec_odo`/`odo_dec`, the `−1` its inverse) and continuous (`odo_prefix_determined`, each output
    bit determined by a finite input prefix).  So the residue unit generates the `ℤ₂`-successor as a
    topological-group automorphism of the escape space — the `2`-adic integer structure carried by
    νF, with the act of pointing as its `+1`.  ∅-axiom. -/
theorem odo_homeomorphism :
    (∀ (f : Nat → Bool) n, dec (odo f) n = f n)
    ∧ (∀ (f : Nat → Bool) n, odo (dec f) n = f n)
    ∧ (∀ {f g : Nat → Bool} (n : Nat), (∀ m, m ≤ n → f m = g m) → odo f n = odo g n) :=
  ⟨dec_odo, odo_dec, fun {_ _} n h => odo_prefix_determined n h⟩

/-! ## §6 — the carry profile: the carry is exactly the leading run of `1`s (the floor distance)

The carry has a precise shape: `carry f n = true` *iff* every bit below `n` is `1`
(`carry_eq_true_iff`) — the carry survives to position `n` exactly along the **leading run of
`1`s**.  And once the carry dies it stays dead (`carry_monotone`: a `false` carry forces `false`
ever after).  So the carry is `true` on an initial segment `[0, R)` and `false` thereafter, where
`R` is the **leading-run length** = the position of the first `0` = the *floor distance* (how deep
the µF floor sits).  The escape (all-`true`) has `R = ∞` (carry true everywhere); a stream with a
floor has finite `R`.  This is the carry-depth as a 213-native invariant — the `+1`'s reach is the
distance to the floor.  All ∅-axiom. -/

/-- ★★★ **The carry is the leading run of `1`s.**  `carry f n = true ↔ ∀ m < n, f m = true`: the
    `+1`'s carry survives to position `n` exactly when every lower bit is `1` — the carry *is* the
    leading run, its length the distance to the first `0` (the µF floor). -/
theorem carry_eq_true_iff (f : Nat → Bool) :
    ∀ n, carry f n = true ↔ ∀ m, m < n → f m = true
  | 0     => by
      constructor
      · intro _ m hm; exact absurd hm (Nat.not_lt_zero m)
      · intro _; exact carry_zero f
  | n + 1 => by
      constructor
      · intro hand
        rw [carry_succ] at hand
        have hc : carry f n = true := by
          cases hcn : carry f n with
          | true  => rfl
          | false => rw [hcn, Bool.false_and] at hand; exact Bool.noConfusion hand
        have hfn : f n = true := by
          cases hf : f n with
          | true  => rfl
          | false => rw [hf, Bool.and_false] at hand; exact Bool.noConfusion hand
        intro m hm
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with h | h
        · exact (carry_eq_true_iff f n).mp hc m h
        · exact h ▸ hfn
      · intro h
        have hc : carry f n = true :=
          (carry_eq_true_iff f n).mpr (fun m hm => h m (Nat.lt_succ_of_lt hm))
        rw [carry_succ, hc, h n (Nat.lt_succ_self n), Bool.true_and]

/-- ★★ **The carry, once dead, stays dead.**  `carry f n = false → carry f (n+1) = false`: a `0`
    absorbs the carry permanently.  So the carry is a step: `true` on `[0, R)`, `false` after. -/
theorem carry_monotone (f : Nat → Bool) (n : Nat) (h : carry f n = false) :
    carry f (n + 1) = false := by
  rw [carry_succ, h, Bool.false_and]

/-- ★★★ **The carry profile (the floor-distance invariant).**  The `+1`'s carry is exactly the
    leading run of `1`s (`carry_eq_true_iff`) and is a step function (`carry_monotone`, once dead
    stays dead) — so it is `true` on an initial segment whose length is the distance to the first
    `0` (the µF floor), `false` beyond.  The carry-depth: the `+1`'s reach equals the floor
    distance; the escape (no floor) has the carry reaching everywhere. -/
theorem carry_profile (f : Nat → Bool) :
    (∀ n, carry f n = true ↔ ∀ m, m < n → f m = true)
    ∧ (∀ n, carry f n = false → carry f (n + 1) = false) :=
  ⟨carry_eq_true_iff f, carry_monotone f⟩

end E213.Theory.Raw.Odometer
