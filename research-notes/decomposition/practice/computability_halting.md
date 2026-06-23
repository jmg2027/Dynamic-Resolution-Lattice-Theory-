# Decomposition: computability / the halting problem (the q=±1 termination tag's residue is the diagonal)

*213-decomposition of "computability / decidability of halting", per `../README.md`. The meeting point of
two corpus themes: the **iterated residue-Lens engine** (`SYNTHESIS.md` §2 finding iii — `q=±1` = whether a
descent terminates) and the **one diagonal** (`cardinality.md`/`godel.md` — the Lawvere fixed-point-free
residue, `q=−1` escape pole).*

## The decomposition

- **Construction `C`** — programs as `Raw`s, **Gödel-coded**: a computation is a tree built by the
  distinguishing act, addressable by its own code (`Lens/Cardinality/Godel.lean:118 Raw.toNat_injective`,
  as in `godel.md`).  No exterior — programs name programs, inside `Raw`.
- **Reading `L_halt`** — the **termination reading**: project each program `a` to "does `a`'s descent
  **terminate** on each input `x`?" — the `q=±1` termination tag (`SYNTHESIS.md` §2 (iii): the dynamic face
  of the residue tag, `+1` = the bracket closes, `−1` = it runs forever).  Indexed by the programs
  themselves (Gödel-coded), this is a **self-cover** `f : A → (A → Bool)` — the *same shape* as
  `cardinality.md`'s count-reading and `godel.md`'s provability-reading; only the feature changes
  ("halts" instead of "is one of these" / "is provable").
- **Residue** — the **diagonal**: a total halt-decider would be a point-surjective `f`, forcing the
  fixed-point-free flip `!` to have a fixed point — impossible (`Lens/Foundations/OneDiagonal.lean:51
  no_surjection_of_fixedpointfree` at `B=Bool`, `:61 cantor_via_lawvere`).  So **no total computable
  termination-decider exists**: the halting problem's undecidability *is* the one diagonal, the `q=−1`
  escape pole (`FlatOntologyClosure.lean:61 object1_not_surjective`).

## Re-seeing the theorems

**The decidability of the `q=±1` termination tag is graded — and the grading is the well-founded modulus.**
- **gcd / Euclidean** (`gcd_euclidean.md`): the descent has a **computable well-founded modulus**
  `M(a,b)=max a b + a` that strictly decreases, so termination is *decidable and always `+1`* — `gcdFuel`
  is **total** ∅-axiom (`Meta/Tactic/NatHelper.lean:618`, no `partial`).
- **Collatz-type** descents: no modulus is known; the `q=±1` tag is *conjectural* (open) — a calibrated
  not-yet-decided instance.
- **general computation** (`L_halt`): the tag is **undecidable** — deciding it is the self-cover whose
  residue is the diagonal.  The *absence* of a computable well-founded modulus is exactly what turns the
  `q=±1` tag from a decidable readout into the diagonal residue.

So "decide whether this descent terminates" climbs: decidable-`+1` (a modulus exists, gcd) → open (Collatz)
→ undecidable (halting = the diagonal).  The **modulus is the boundary** between a readable `q` and the
diagonal — the "computable narrowing interval" doctrine (CLAUDE.md "Infinity is the residue's shape") read
at the level of *termination itself*.

## Revelation (collapse + forcing)

**Collapse — halting, Cantor, and Gödel are one self-cover, three features.**  The halting problem is not a
new impossibility: it is `f : A → (A → Bool)` with the feature "halts", exactly `cardinality.md`'s diagonal
with the feature "is one of these" and `godel.md`'s with "is provable".  One construction
`g a := !(f a a)`, three readings (`one_diagonal_generates`, `OneDiagonal.lean`).  The famous trio
Cantor / Gödel / Turing is the count-Lens, provability-Lens, and termination-Lens **of the same residue**.

**Forcing — the dynamic `q=±1` tag and the one-diagonal are one object.**  This closes the loop between
this session's arc and the foundational core: the residue tag's *dynamic* face (does the iterated residue-Lens
descent terminate?) and the *one diagonal* (the limitative residue) are not two themes — **deciding the
`q=±1` termination tag of an arbitrary descent IS the self-cover whose residue is the diagonal.**  The
static face (the Legendre symbol `(a/p)`, `modular_arithmetic.md`/finding (i)), the dynamic face (Euclidean
termination, finding (iii)), and the *meta* face (the undecidability of that termination = the diagonal) are
three readings of the single `q=±1` object.

## Verified Lean anchors (file:line:theorem — grep-confirmed, scans this session)

- `Lens/Foundations/OneDiagonal.lean:43 lawvere_fixed_point`, `:51 no_surjection_of_fixedpointfree`
  (the abstract halting obstruction — no point-surjection of `A → (A→Bool)`), `:61 cantor_via_lawvere`,
  `:101 one_diagonal_generates` (one construction, the trio). **PURE (11/0).**
- `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective` — the residue as the diagonal at
  `A=Raw`, the `q=−1` escape pole. **PURE (7/0).**
- `Lens/Cardinality/Godel.lean:118 Raw.toNat_injective` — programs Gödel-coded (the self-reference
  `L_halt` needs, shared with `godel.md`).
- `Meta/Tactic/NatHelper.lean:618 gcdFuel` — the *decidable-`+1`* contrast: a descent with a computable
  well-founded modulus terminates totally (`gcd_euclidean.md`).
- Cross-frame: `cardinality.md` (count-Lens diagonal), `godel.md` (provability-Lens diagonal),
  `SYNTHESIS.md` §2 (iii) (the iterated residue-Lens engine, `q=±1` = termination).

## BUILT vs ABSENT

- **BUILT (∅-axiom):** the diagonal residue (`no_surjection_of_fixedpointfree` — the abstract "no total
  halt-decider" at `B=Bool`), the Gödel coding (`Raw.toNat_injective`), and the decidable terminating
  contrast (`gcdFuel` total).
- **ABSENT (predicted-not-built):** a named `TuringMachine` / `halts` predicate / `Collatz` object, and the
  *packaged* "halting problem is undecidable" as a statement about a built computation model — only the
  abstract diagonal is built (the same status as `godel.md`'s named-Gödel-sentence absence; the named
  object is the construction the calculus *predicts*, not yet instantiated).

## Touches the model?

**No new primitive — `cardinality.md`'s one diagonal with the termination feature, unified with the
iterated residue-Lens engine.**  Both invariants hold: the reading is a self-cover (the diagonal engine), and
the `q=±1` tag is the termination bit whose *meta*-undecidability is that very diagonal.  The new datum is
the **unification**: the dynamic `q=±1` tag (does the descent terminate?) and the one-diagonal residue
(Cantor/Gödel) are one object — the well-founded modulus is the boundary between a *readable* `q` (gcd, `+1`)
and the *diagonal* `q` (halting, undecidable). The residue-tag spine and the one-diagonal spine meet here.
