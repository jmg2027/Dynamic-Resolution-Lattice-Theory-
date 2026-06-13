# Chapter 6 — Reading: the Orbit, the Residue, the Unit

The earlier chapters dismantled the imported reading and rebuilt the structure as a Lens-tower
readout. This chapter says what the readout, taken on its own honest terms, *means* — and ends by
separating, once and for all, what in this entire body of work is foundational from what is readout.

## 6.1 The orbit generates the residue

Read the order-2 orbit as motion. Two things turn — the pair `(s(n), s(n+1))` — tracing the fixed
conic of §3.2. Their turning *is* the generation of a residue: at every layer the conserved Cassini
unit is reproduced, never zero, never reached. The 2-1-3 of atomicity is exactly this:

> **two orbit, generating one, seen as three.**
> `PhiResidueGlue.orbit_two_generates_residue_seen_as_three`: `NT = 2` (the orbiting pair); `W n =
> NS − NT` (the residue the orbit carries, the same at every layer); `NS = NT + 1` (the pair plus
> the residue it generates).

The three is not three independent atoms. It is the two-that-turn plus the one-they-generate. And it
is genuinely structural, not a coincidence of small numbers: the orbit order is `NT`, the Cassini
window is `NT + 1 = NS` consecutive terms, the residue value is `NS − NT`. The atomic counting and
the orbit geometry are one `2-1-3`.

## 6.2 The unit at three scales

The residue the orbit generates is the unit `1`, and it is the same `1` read at three scales — and
because Chapter 4 isolated the native kernel, we can say which scale is which:

> `PhiResidueGlue.residue_unit_three_scales`: the orbit's conserved determinant `det Pⁿ` equals
> `NS − NT` (algebra); the convergent cross-determinant `W n` equals `NS − NT` (analysis); and
> `NS − NT = 1 = det P` (atomicity).

Natively, all three are the difference-Lens unit — the `m − n` of the directed count-pair at the
glue value `NS − NT`. The "imaginary unit," the "Pell unit," the "discriminant glue" were three
imported names for the one period-2 sign of §2.4 read at the value `1`.

## 6.3 Frozen equals dynamic

The deepest reading the tower supports is that the residue is *what the dynamic never closes*. The
golden ratio φ has two faces — frozen (the algebraic fixed point, the characteristic relation of
`P`) and dynamic (the limit of the Pell convergents). They are one object:

> `Real213.PhiFrozenDynamic.frozen_eq_dynamic_phi`: the convergent Cauchy limit *is* the closed-form
> φ cut; and the convergent stays exactly the unit `1` off the frozen relation
> (`fib_cassini_norm`), never reaching it (`convergent_never_frozen`); the frozen φ's discriminant
> is `P`'s characteristic discriminant (`phi_discriminant_is_P_charpoly`).

The residue is the gap between approach and limit — `det s 0 ≠ 0` forever (§3.2). The dynamic
generates the unit at every step precisely *because* it never closes; generation and non-closure are
one fact. This is `the_form_of_the_residue`'s source-without-enclosure, read at the orbit: a source
that keeps producing the unit is a dynamic that never reaches its frozen limit.

## 6.4 What is foundational, and what is readout

The book's final accounting. Of everything assembled here, two strata must be kept apart.

**Readout layer (this book's subject).** The Cassini, the determinant multiplier law, the conic, the
divergence floor, the axis `{2,4,6}`, the discriminants, the regular representation, the
frozen=dynamic identification. All genuine, all `∅`-axiom, much of it original (the multiplier law
`det(n+1) = q·det(n)` most of all). All of it stands at least three Lens-steps above the residue —
quadratic (rung two) and differenced (rung three). None of it is foundational. Several pieces are
imported substrate (the unit cardinalities, the modular generators, the CM points) with a native
kernel retro-fitted on top; the honest pieces are the difference-Lens unit and the determinant law.

**Foundational layer (this book's floor, developed elsewhere).** The residue itself — the slash, the
self-pointing — and its first Lens, the count. Here live the genuinely foundational results: the
initial algebra and final coalgebra of the self-pointing functor (`Theory.Raw.CoResidue`,
`Lambek`), the residue as source-without-enclosure (`the_form_of_the_residue`), atomicity forcing
`(NS, NT, d) = (3, 2, 5)`. No integer, no multiplication, no determinant appears at this layer. It is
where "no exterior" and "assume nothing" actually bite.

The one thread that runs cleanly from the floor to the readout is the descent of Chapter 5: the disc
edifice's last fact, `NT` is a non-square count, is the count-Lens shadow of the residue's first
slash, `NT = leaves(a/b) = 1 + 1`.

## 6.5 Coda

The orbit-climbing structure looked like the imaginary quadratic fields and the modular curve. It is
not them; it is one residue read through a fixed tower of Lens choices, and the resemblance is
arithmetic coincidence at the readout layer plus a discipline lapse in the naming. Stripped to its
floor, the whole edifice says one thing the residue can say in its own voice:

> *The first distinguishing, counted, is two; and two is not a square.*

Everything above is the difference-Lens speaking — true, useful, and not the foundation. The
foundation never left the slash.
