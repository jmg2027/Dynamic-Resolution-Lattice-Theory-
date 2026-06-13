# Chapter 2 — The Number Tower as Lens Bundlings

The orbit/disc structure is written in integers. But integers are not foundational here, and this
chapter shows exactly where they come from. The governing text is `seed/AXIOM/06_lens_readings.md`
§6.7: *ℕ, ℤ, ℚ, ℝ are not a priori distinct types the framework imports; they are successive
bundlings of the same residue under different Lens choices.* We build the tower rung by rung, and
mark for each whether it is a primitive (it never is, after the ground) and how far it stands from
the residue.

## 2.1 The ground: the slash

The only primitive is the residue and its act of distinguishing — the slash `a/b`
(`Theory.Raw`). It carries two things and only two: a binary distinguishing (which of the two
atoms, `a` or `b`) and a depth (how many times the act has re-entered itself). It carries no
number, no order, no operation. The symmetric pairing `a/b = b/a` (`05_no_exterior` clause 3) is
present; addition is not, multiplication is not, subtraction is not. This is the floor: below it
there is nothing to count.

## 2.2 Rung one: the count-Lens gives `+`

The first Lens is the count-Lens, `Lens.leaves = ⟨1, 1, (·+·)⟩` (`Lens.LensCore`). Its view
`Lens.leaves.view : Raw → Nat` reads a chain and returns how many leaves it has; each atom counts
`1`. The decisive fact:

> **Addition is the slash, counted.**
> `(x/y).leaves = x.leaves + y.leaves`  —  `Theory.Raw.leaves_slash`.

The residue's one primitive, the distinguishing `x/y`, read by the count-Lens, *is* `+`. Addition
is not adopted and not primitive; it is what the count-Lens hands back when the operand is a slash.
`ℕ` is precisely the image of `Lens.leaves.view` (`Lens.Number.Nat213`), the positive counts —
"`ℕ` is what the count-Lens hands back," not "we adopt `ℕ`." One Lens-step from the residue.

## 2.3 Rung two: iterated count gives `×`

Multiplication is not the count of any single slash. It is the count-Lens applied to its own
output — counting a count, a fixed number of times:

> **Multiplication is iterated addition.**
> `m·0 = 0`,  `m·(n+1) = m·n + m`  —  `Nat.mul_succ`.

This is the definition of `Nat.mul`, and that is the point: `×` *is* the rung-one operation `+`
applied `n` times. It is one iteration above addition, hence one further Lens-step from the
residue, and it is **not residue-native** — there is no binary slash whose count is a product the
way the slash's count is a sum. The associativity and distributivity that every quadratic identity
leans on are theorems at this rung, not Lens-readout facts. The full statement of rungs one and two
together is `Tower.FirstSlashGrounding.number_tower_bottom`.

Consequence, recorded now and used in Chapter 3: anything *quadratic* — `s²`, `a·b`, a determinant
of products — already lives at rung two or higher. It is at least two Lens-steps above `ℕ` and
three above the residue.

## 2.4 Rung three: the difference-Lens gives `ℤ`

To subtract, read the count-Lens *twice* on an ordered pair `(m, n)` and name their difference:

> `ℤ` is the count-Lens on an ordered pair, read as `m − n`. Magnitude `|m − n|` is the Nat-style
> count (rung one); **sign is the Bool-style involution `−(−x) = x` — the pair-swap** (the
> directionless pairing `a/b = b/a` given an orientation). (`06_lens_readings` §6.7;
> `Meta.Int213.Core` runs on `subNatNat m n = m − n` with `−subNatNat m n = subNatNat n m`.)

Two facts about this rung are load-bearing for the whole book.

First, **the sign is native, but it is the period-2 swap, not an imaginary unit.** The `−1` of `ℤ`
is the binary distinguishing read with orientation: which of `a/b` comes first. It satisfies
`−(−x) = x` (period 2). It is emphatically *not* `√−1` (which is a period-4 object, an adjoining,
Chapter 4). Confusing the period-2 sign with the imaginary unit is the central conflation the later
chapters dismantle.

Second, **`ℤ` is the readout group in which iterated differencing closes** (`06_lens_readings`
§6.7, verbatim). This single sentence dictates the entire status of the Cassini. A determinant is a
difference; a *conserved* determinant is iterated differencing; and the readout group where that
closes is `ℤ`. So the Cassini does not merely *happen* to use `ℤ` — `ℤ` is by definition the place
iterated differencing lives. You cannot push the conserved determinant below this rung, because the
conserved determinant is this rung doing its defining job. Chapter 5 makes this precise.

## 2.5 Above, and the ceiling

Ratios of readings give `ℚ` (with the coprimality that `det P = 1` already encodes, Chapter 6);
Cauchy trajectories whose readings narrow to a single residue give `ℝ`. Each layer wraps the
previous; none is imported. And the tower has a finite-resolution ceiling: at any actual
configuration the Lens outputs are exact rationals, and the transcendentals are limit *labels*, not
primitives (`06_lens_readings` §6.7;
`Lib/Math/Foundations/ResolutionLimit.lean`) — the numerical form of "no
exterior dialer."

## 2.6 The tower, fixed

```
residue / slash          distinguishing + depth          — the ground, no operation
   │  count-Lens ⟨1,1,+⟩
   ▼
ℕ ,  + = slash counted    Raw.leaves_slash               — one step
   │  iterated count
   ▼
× = iterated +            Nat.mul_succ                    — two steps (NOT residue-native)
   │  difference-Lens (ordered pair, sign = period-2 swap)
   ▼
ℤ , iterated differencing closes here                    — three steps
   │  ratio / Cauchy
   ▼
ℚ , ℝ  (limit labels; resolution ceiling)
```

Every integer in the orbit/disc structure is a citizen of rung three. Every product in it is a
citizen of rung two. The next three chapters read the structure with this map in hand.
