# Chapter 5 — The Descent to the First Slash

Chapter 4 isolated a native kernel. This chapter takes the kernel's last surviving fact — `NT` is a
non-square count — and grounds it one rung lower still, in the residue's first act of distinguishing.
At the bottom there is no integer and no "discriminant," only the slash and the count of it.

## 5.1 `NT` is the first distinguishing, counted

The atomic count `NT = 2` is not a bare constant. It is the count-Lens reading of the first slash.
The two atoms each count one leaf (`leaves a = leaves b = 1`), and the first distinguishing joins
them:

```
leaves(a/b) = leaves a + leaves b = 1 + 1 = NT.
```

The first equality is `Theory.Raw.leaves_slash` (Chapter 2's rung one: addition is the slash
counted). The second is arithmetic. So `NT` is *what the count-Lens hands back when the operand is
the first distinguishing.* The atomicity count and the residue's first slash are the same object,
seen through one Lens.

## 5.2 The descent theorem

The whole imported phenomenon of Chapter 4 — "disc `−2` is skipped between the order-4 and order-6
axes" — now lands, `ℤ`-free, on the residue. Three facts, each one Lens-step lower than the last:

> `Tower.FirstSlashGrounding.disc_neg_two_descends_to_first_slash`:
> 1. `(x/y).leaves = x.leaves + y.leaves`  — `+` is the slash counted (the count-Lens at work);
> 2. `a.leaves + b.leaves = NT`  — the first distinguishing counts to `1 + 1 = NT`;
> 3. `¬ ∃ m, m·m = NT`  — `NT` is a non-square count.

Fact 3 is the entire residue-native content of "disc `−2` is skipped." Everything above it —
`t² − 4`, "imaginary quadratic field," "elliptic `SL₂` trace," the "order-8 lift" — is the
difference-Lens and number-Lens dressing of this one count-Lens fact:

> **`2 = leaves(a/b) = 1 + 1` is not `m·m` for any count `m`.**

The point `−2` carries no rotation axis for the same reason `2` carries no square: there is no count
that, counted that-many times, gives the first distinguishing. That is all "disc `−2` skipped" ever
meant.

## 5.3 The number-tower bottom, as one theorem

The descent assembles into the bottom of the number tower stated as a single theorem chain — the
three derived rungs beneath every quadratic readout, then the residuum:

> `Tower.FirstSlashGrounding.number_tower_bottom`:
> 1. `(x/y).leaves = x.leaves + y.leaves`  — `+` = the slash counted (rung one);
> 2. `m·0 = 0`, `m·(n+1) = m·n + m`  — `×` = iterated `+` (rung two; not residue-native);
> 3. `¬ ∃ m, m·m = NT`  — a square count is `m·m`; `NT` is not one.

Read upward, this is the genealogy of the Cassini. The Cassini is *quadratic*, so it needs rung two
(`×`), which is iterated rung one (`+`), which is the slash counted. The Cassini is a *difference*,
so it needs the rung above — `ℤ`, the difference-Lens. Hence the Cassini stands at least three Lens-
steps above the residue: **readout-layer, not foundational**, exactly as Chapter 3 anticipated, now
proved as a chain rather than asserted.

## 5.4 Why the descent stops here

Below rung one there is no count — only the slash (distinguishing) and depth. There is no operation
to ground `+` in, because `+` *is* the first thing the residue produces under a Lens; beneath it the
residue is not yet counted at all. So the descent terminates at fact 5.2(2): `NT = leaves(a/b)`. The
slash itself is the floor (`05_no_exterior` §5.1: no exterior, nothing further in). One cannot ask
"and what is the slash made of," because that question presupposes an exterior the framework denies.

The chain is therefore complete and bottomed: residue/slash → count (`+`) → iterated count (`×`) →
difference (`ℤ`) → the disc/axis/Cassini readout. The single fact that survives all the way to the
floor is that the first distinguishing's count is non-square. The final chapter reads what this whole
structure *says*.
