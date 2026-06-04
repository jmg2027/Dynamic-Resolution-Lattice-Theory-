import E213.Theory.Atomicity
import E213.Lib.Physics.Simplex.Counts

/-!
# FalsifierRosterForced — the DRLT falsifier integers are *forced* polynomials in (NS, NT, d)

The DRLT falsifier roster (`catalogs/falsifiers.md`) is a list of measurable integers — the
Cabibbo denominator `22`, the muon prefactor `192`, the baryon skeleton `6`, the generation
count `3`, … — each read as a polynomial in the atomic triple `(NS, NT, d) = (3, 2, 5)`.  On its
own that is curve-fitting: any small integer is *some* polynomial in three free numbers.  What
makes the roster a falsifier surface rather than a fit is that the triple is **not free** — it is
the *unique* one forced by two ∅-axiom theorems:

  * **`atomic_iff_five`** (`Theory/Atomicity/Five`) — `d = 5` is the *only* atomic count (the
    `2a + 3b` Bézout argument singles it out);
  * **`pair_forcing`** (`Theory/Atomicity/PairForcing`) — `(NT, NS) = (2, 3)` is the *only*
    coprime pair with a unique atomic candidate.

So the falsifier integers are consequences of one forced triple, not six independent dials.
This file states that as a single super-theorem: the two forcing `iff`s, the triple they force,
and the headline falsifier integers as polynomials in it.

**Scope honesty** (CLAUDE.md "DRLT-validation-as-the-goal"): this is the *physics branch's*
falsifier gate — one domain's surface, not THE yardstick the repo is measured by.  The
load-bearing content is the **forcing** (the integers follow from the unique triple); the
numerics alone would be a research note.  All ∅-axiom (`decide` + the two forcing theorems).
-/

namespace E213.Lib.Physics.Foundations.FalsifierRosterForced

open E213.Lib.Physics.Simplex.Counts (NS NT d binom)

/-- ★★★ **The falsifier roster is forced, not fitted.**  One theorem covering the falsifier
    surface:

    * **the forcing** — `d = 5` is the unique atomic count (`atomic_iff_five`), and
      `(NT, NS) = (2, 3)` the unique coprime pair with a unique atomic candidate (`pair_forcing`);
      so the triple `(NS, NT, d) = (3, 2, 5)` is forced;
    * **the falsifier integers as polynomials in the forced triple** —
      F1 atomicity `d = 5`; F2 generation count `C(NS, NT) = 3` (no 4th generation);
      F8 Cabibbo denominator `d² − NS = 22` (λ = `d`/22); F22/F26 baryon-skeleton `NS·NT = 6`;
      F26 η_B denominator exponent `d·NT = 10`; F24 muon prefactor `(NS²−1)(d²−1) = 192`;
      F15/F19 Bell-coincidence / Z-width count `2·NS·NT = 12`; F21 Koide `Q = NT/NS = 2/3`
      (cross-multiplied `3·NT = 2·NS`).

    Each integer is a consequence of the unique forced triple — measure any of them outside its
    bracket and the *triple* is refuted, not a free parameter retuned.  ∅-axiom. -/
theorem falsifier_roster_forced :
    -- the unique forced atomic triple (not a fit)
    (∀ n : Nat, E213.Theory.Atomicity.Five.Atomic n ↔ n = 5)
    ∧ (∀ p q : Nat, 2 ≤ p → p < q →
        (E213.Theory.Atomicity.PairForcing.count p q = 1 ↔ (p = 2 ∧ q = 3)))
    ∧ (NS = 3 ∧ NT = 2 ∧ d = 5)
    -- the headline falsifier integers, each a polynomial in (NS, NT, d):
    ∧ (d = 5)                                   -- F1  atomicity (d ≠ 11, 26)
    ∧ (binom NS NT = 3)                         -- F2  N_gen = C(NS, NT) = 3 (no 4th generation)
    ∧ (d * d - NS = 22)                         -- F8  Cabibbo denominator 22 = d² − NS
    ∧ (NS * NT = 6)                             -- F22 m_p/m_e skeleton, F26 η_B leading 6 = NS·NT
    ∧ (d * NT = 10)                             -- F26 η_B denominator exponent 10 = d·NT
    ∧ ((NS * NS - 1) * (d * d - 1) = 192)       -- F24 muon prefactor 192 = (NS²−1)(d²−1)
    ∧ (2 * NS * NT = 12)                        -- F15/F19 Bell ≤ 12, Z widths 12 = 2·NS·NT
    ∧ (3 * NT = 2 * NS) :=                       -- F21 Koide Q = NT/NS = 2/3 (cross-multiplied)
  ⟨E213.Theory.Atomicity.Five.atomic_iff_five,
   E213.Theory.Atomicity.PairForcing.pair_forcing,
   by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide⟩

end E213.Lib.Physics.Foundations.FalsifierRosterForced
