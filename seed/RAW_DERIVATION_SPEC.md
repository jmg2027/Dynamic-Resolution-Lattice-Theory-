# Raw-derivation: three technical readings

> **Canonical**: when "X is derived from Raw" appears in DRLT
> commentary, papers, or AXIOM chapters, this file pins which
> reading is meant.  Implementation-level evidence in
> `lean/E213/`; meta-scan evidence in `research-notes/G104`.

The phrase "everything in DRLT is derived from Raw" has three
distinct technical meanings.  Each is independently TRUE or FALSE
on a different basis.  Conflation is the common error.

This file articulates the three readings and records which holds.

---

## Reading (α) — Logical derivability

**Statement**.  Every theorem in `lean/E213/` closes under Lean's
kernel + the 4-clause Raw axiom set (no further axiom).

**Status**.  **TRUE.**  Verified by `#print axioms` on every
`★`-marked theorem.  No `Classical.choice`, no `native_decide`, no
`sorryAx`, no external axiom.  See `STRICT_ZERO_AXIOM.md` for the
canonical PURE/DIRTY ledger and `seed/AXIOM/04_falsifiability.md`
§5.2.1 for the falsifiability rule that enforces this.

**Independently verified**:
  · G95 dep-purity audit on every cited core lemma.
  · Parallel branch closure of all DIRTY-cited remnants
    (N5 / N6 centralisations).
  · DRLT is **PURE-bounded on Lean 4 core** — no axiomatic
    escape hatch downstream of the 4-clause axiom.

The mechanical auditor is `#print axioms`.  Reading (α) is the
**logical** version: derivability under the kernel's notion of
proof.

---

## Reading (β) — Structural-content derivability

**Statement**.  The mathematical content of DRLT — specifically
the inevitability chain Raw → (NS, NT, d) = (3, 2, 5) → 6-theorem,
including the alive predicate (Clause-4 recursive per
`AliveDerivation.alive_iff_clause4_alive`) — is **provably
derivable from the 4-clause Raw axiom alone**.

**Status**.  **TRUE.**  The atomicity / Pell-unit invariant /
ZOmega^× = C_6 / dual-filling χ-sum chain constructs the corpus's
headline numbers (`α_em`, `m_t/m_c`, `η_B`, ...) without invoking
external content — verified by the substantive branches' work and
catalogued in `catalogs/precision-results.md`.

Reading (β) is the **structural-mathematical** version:
the mathematics itself, not just its kernel-checkability.

---

## Reading (γ) — Operational / definitional reduction

**Statement**.  Every theorem's **proof body** and **type
signature** Expr should transitively reduce to references to Raw
atoms via Expr-level forward edges.

**Status**.  **FALSE in general.**  Empirically (G102 + G103 §1 +
G104 §2): only ~15 % of E213 declarations reach a Raw atom via
Expr-level forward edges within finite depth.

The remaining ~85 % use carrier types like:

  · `Cochain n k := Fin (binom n k) → Bool`
  · `Cut := Nat → Nat → Bool`
  · `binom` — Nat arithmetic
  · `Lens.view`, `Lens.combine` — Lens projections

These are **generic Lean infrastructure**, defined in terms of
`Nat`, `Bool`, `Int`, `Fin`, not in Raw-construction terms.  Their
Expr neither contains Raw atoms in its body nor in its type
signature.

**(γ) being false does not undermine (α) or (β).**  The architecture
is: **Raw-derived mathematical content layered on top of generic
Lean computational infrastructure**.  The math is Raw-native; the
substrate is Lean stdlib.

### What (γ) would require to be true

A version of DRLT where every carrier type unfolds to a Raw
construction at the Expr level — for instance, `Cochain` defined
as a recursive function over `Raw.fold`, `binom` defined as
counting Raw sub-trees, etc.  This is **not the current design** and
**not desirable** — the chosen substrate (Nat/Bool/Fin) is what
makes the corpus mechanically tractable.

### Empirical evidence (G104 §2)

| Metric | Body-only edges | Body ∪ type edges |
|--------|----------------:|------------------:|
| Reach Raw | 1,111 (14.8 %) | 1,218 (14.7 %) |
| Max depth | 3 | 3 |
| Mean depth | 1.13 | 1.09 |

Adding type-signature edges barely changes the reach percentage.
The encapsulation isn't at the body-vs-type distinction; it's at
the **definitional layer** — carrier types are defined in non-Raw
terms.

---

## Why the distinction matters

The three readings answer different questions:

| Reading | Question | Answer | Verified by |
|---------|----------|--------|-------------|
| (α) | "Is the proof logically closed under the Raw axiom set?" | YES | `#print axioms` |
| (β) | "Does the mathematics derive from Raw structurally?" | YES | substantive branch proofs |
| (γ) | "Does every Expr reduce to Raw atoms operationally?" | NO | G102/G103/G104 meta-scans |

A statement like "DRLT is grounded in Raw" usually means (α) + (β).
Citing G102's "14.8 % reach Raw" as a counter-claim only contradicts
(γ), which is not what (α)/(β) require.

Conflation is the failure mode.  Specifying which reading is at
stake removes the confusion.

---

## Self-check before writing "derived from Raw"

When a future doc or commit message uses the phrase, the writer
should be able to point to one of (α) / (β) / (γ) as the intended
reading.  If none fits cleanly, the claim is unclear and needs
disambiguation.

---

## Cross-references

  · `seed/AXIOM/04_falsifiability.md` §5.2.1 — the axiom-set
    constraint that grounds (α).
  · `STRICT_ZERO_AXIOM.md` — canonical PURE/DIRTY ledger
    enforcing (α).
  · `research-notes/G104_raw_derivation_three_levels.md` — full
    quantitative evidence behind this spec.
  · `research-notes/G102_full_expr_callgraph.md` — Expr-level
    call graph methodology.
  · `lean/E213/Theory/Atomicity/PairForcing.lean` etc. — substantive
    derivations realising (β).
  · `lean/E213/Lib/Math/Cohomology/Cochain/Core.lean` — example
    of generic-substrate carrier type (`Cochain n k := Fin _ → Bool`).
