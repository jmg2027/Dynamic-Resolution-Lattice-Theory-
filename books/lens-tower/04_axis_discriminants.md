# Chapter 4 — The Axis and the Discriminants

This is the chapter where the imported names are densest — `{2,4,6}`, "discriminant," `ℤ[i]`, `ℤ[ω]`,
the modular generators, the crystallographic restriction — and where the native/imported separation
must therefore be made most carefully. The procedure is the same throughout: state the `∅`-axiom
theorem honestly, then ask what survives deleting every imported word.

## 4.1 The axis `{2,4,6}` and what is native in it

Classically the unit groups of the imaginary quadratic rings have orders exactly `{2, 4, 6}`:

> `ImaginaryQuadraticUnitTrichotomy.imaginary_quadratic_unit_trichotomy` — the axis is exactly
> `{2, 4, 6}`; every ring past the two special points collapses to `{±1}`, order `2`
> (`unitForm_generic_axis`).

True, pure — and, by the file's own docstring, *the classical Dirichlet trichotomy made `∅`-axiom*.
The proof is a generic Diophantine overshoot (`a² + d·b² = 1 ⟹ b = 0` for `d ≥ 2`); it never uses
`d = 5`, never mentions `NS, NT`. The values `4` and `6` come from `ℤ[i]`, `ℤ[ω]`, structures whose
definitions contain no atomic count.

So what is native? Exactly one order:

> **The only un-adjoined automorphism is the period-2 swap** `a/b = b/a`, read as `−(−x) = x` — the
> difference-Lens sign of §2.4. Every other axis is forced back to it (`unitForm_generic_axis`).

Orders `4` and `6` are not native; they are **adjoined and derived** — they appear only after
adjoining a square root of a residue (`√−1`, `√−NS`), and the trichotomy proves nothing else
survives. The repository's own framing makes the native fold visible:
`{2,4,6} = 2·{1,2,3}` (`SpiralAxisCrystallographic.spiral_axis_is_even_crystallographic`), the
period-2 sign covering three base counts. The "doubling by the central `−1`" is native-flavored; the
parent set `{1,2,3,4,6}` it is carved from is the crystallographic restriction, imported lattice
theory with no native reason in 213.

## 4.2 The discriminants are count-Lens readouts

Strip the word "discriminant" — a `t² − 4d` quantity from quadratic-form theory — and the three
numbers are count-Lens readings of the atomic pair `{NT, NS} = {2, 3}` at three integer-trace
regimes (`AxisSeedTrichotomy`):

| regime (integer trace) | readout | native form |
|---|---|---|
| trace `NS = 3` (the pair-sum, the escaping orbit) | `+5` | `NS + NT = d` |
| trace `±1` (the unit) | `−3` | `−NS` |
| trace `0` (the bare floor) | `−4` | `−4·g`, the universal `−4·det` term at zero trace |

The native triple is `{NT, −NS, NS+NT}` — the radicands proved in
`AxisSeedTrichotomy.axis_seed_trichotomy`. The `−` on `−NS` is the single essential sign (the
difference-Lens swap); the other two regimes are sign-`+`. "Discriminant" is the imported name; the
count-Lens triple is the content.

## 4.3 The skipped point: `−2 = −NT`

`−2` is missing from the discriminant list, and the imported reason — "`ℤ[√−2]` has unit group only
`{±1}`" — has a native shadow that is the whole truth:

> **`−2 = −NT`, and `NT` is a non-square count.** No integer trace gives discriminant `−2`, because
> that needs `t² = 2`, and `2` is not a perfect square
> (`DiscNegTwoSkipped.no_nat_sqrt_two`); the elliptic integer traces `{−1, 0, 1}` give exactly
> `{−3, −4}`, never `−2` (`DiscNegTwoSkipped.elliptic_traces_skip_disc_neg_two`).

So `−NS` (trace `±1`) and `d` (trace `NS`) are realized by integer counts; `−NT` is not. It is the
one count among the three that no count squares to. Its surd `√NT = √2` reappears only one tier up,
at order `8` — and order `8` is the first non-crystallographic order (`φ(8) = 4 > 2`), off the axis
entirely. The native form of the skip, with no `ℤ`, no "discriminant," no "trace," is
`DiscNegTwoSkipped.NT_is_nonsquare_count`:

```
1² < NT < 2²   ∧   ¬ ∃ m, m·m = NT.
```

The first distinguishing's count, `NT = 2`, is a count strictly between consecutive count-squares —
the leaf-count of no squared chain. Chapter 5 grounds even this in the slash.

## 4.4 The CM points and the modular generators — a clean exhibit of import

The order-4 and order-6 points (`disc −4`, `i`; `disc −3 = −NS`, `ω`) and the modular generators
`S, U` admit a genuine *homomorphism* into the matrix picture — the regular representation
`ℤ[i] → M₂(ℤ)` sends the Gaussian unit `i` to `S`:

> `UnitsToModular.repI_hom` (a ring homomorphism), `UnitsToModular.repI_I : repI i = S`.

This is honest as far as it goes, but it is the clearest exhibit of import in the book, and must be
labeled as such: `repI i = S` holds **by `rfl`, because `S` is defined as `repI ⟨0,1⟩`.** It is a
construction-tautology, not a 213 primitive at work. The genuinely native content it gestures at is
only what Chapter 2 already gave: the period-2 swap is the one native automorphism, and
`det = NS − NT = 1` is the glue. Being in `SL₂` *is* being on the `q = 1` Cassini floor
(`UnitsToModular.modular_generators_on_q1_floor`) — that connection is real, and it is a connection
to the difference-Lens unit, not to the modular group as such.

## 4.5 The native kernel, isolated

Delete every imported name — `ℤ[i]`, `ℤ[ω]`, "discriminant," "modular," "crystallographic,"
"genus," "CM" — and exactly this survives:

- the counts `(NS, NT, d) = (3, 2, 5)`, with `NS + NT = d`, `NS − NT = 1`, `NS · NT = 6`
  (`Mobius213OneAsGlue`);
- `det P = NS − NT = 1` as the glue — the difference-Lens unit (`mobius_det_eq_ns_minus_nt`);
- the period-2 swap (`−(−x) = x`), the one native automorphism;
- the radicand triple `{NT, −NS, NS+NT}` as count-Lens readouts;
- `NT` is a non-square count (`no_nat_sqrt_two`).

Everything else — the unit cardinalities `4, 6`, the regular representations, the CM points, the
crystallographic set, the algebraic numbers `√2, ω, φ` — is imported substrate onto which this
native kernel is retro-fitted by arithmetic coincidence (`6 = NS·NT`, `5 = NS + NT`, `−3 = −NS`).
`∅`-axiom-correct, and not native. The next chapter shows the kernel itself is the shadow of a single
slash.
