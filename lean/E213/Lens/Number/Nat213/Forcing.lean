import E213.Lens.Number.Nat213.Bridge
import E213.Lens.Number.Nat213.Generation
import E213.Lens.Number.Nat213.Irreducible
import E213.Lens.Foundations.UniversalDistinguishing

/-!
# Lens.Number.Nat213.Forcing — the FTA's carrier is forced by the distinguishing (∅-axiom)

The **descent leg**, M5 — the *forcing* half (the `the_descent_leg` frontier).  The
FTA capstone (`FTA.fta`) generates arithmetic over `Peano.Nat213`; this file ties that carrier back to
the **primitive act of distinguishing**, and shows a distinguishing-*blind* reading provably cannot
carry the factorization structure.

**Honest framing (the §5.1 wall, not hidden).**  `Peano.Nat213` is its own inductive — an *ergonomic
parallel* to the Raw chain, not literally `Raw` (`Peano.lean` says so).  The link to the act is the
**injective bridge** `Bridge.toRaw : Peano.Nat213 → Raw` whose successor *is* the distinguishing:
`toRaw (succ k) = Raw.succ (toRaw k) = slashOrSelf (toRaw k) Raw.b`
(`peano_succ_is_distinguishing`).  So the claim earned here is **recognition, not genesis** — the
FTA's carrier is recognized, element by element, as the chain built by iterated self-distinguishing
against the atom `b`.  That is the marathon's wall #1, stated as a measured boundary.

**The forcing.**  Under the count reading (`Raw.value`, which *uses* the distinguishing via `+`),
`four` and `five` are separated (`4 ≠ 5`) — exactly the data that makes `four` composite and `five`
irreducible (`Irreducible.four_not_irreducible`, `five_irreducible`).  Under the distinguishing-blind
reading (`Generation.degLens`, constant combine), every element collapses to `1`
(`Generation.deg_view_one`), so `four` and `five` become indistinguishable — the blind reading cannot
even tell a composite from a prime, hence cannot carry the FTA.  The factorization structure is
**forced by the distinguishing**, not decorative.  ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Forcing

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Irreducible (Irreducible five_irreducible four_not_irreducible)

/-- **Peano's successor is the distinguishing** (under the bridge): `toRaw (succ k)` is `toRaw k`
    wrapped by a `slash` against the atom `b` — `Raw.succ` *is* `slashOrSelf · Raw.b`
    (`Generation.succ_is_distinguishing`).  This is the load-bearing link from the FTA's carrier to
    the primitive act. -/
theorem peano_succ_is_distinguishing (k : Nat213) :
    Bridge.toRaw (Nat213.succ k) = Raw.succ (Bridge.toRaw k) :=
  Bridge.toRaw_succ k

/-- The distinguishing-blind reading collapses every `Nat213`'s Raw image to `1` — it discards the
    `slash` structure the count is built from. -/
theorem blind_collapses (m : Nat213) :
    Generation.degLens.view (Bridge.toRaw m) = 1 :=
  Generation.deg_view_one (Bridge.toRaw m)

/-- ★★★ **The FTA's factorization structure is forced by the distinguishing.**
    `five` is irreducible and `four` is not (an FTA-level distinction over `Nat213`); the
    distinguishing-blind reading `degLens` *identifies* their Raw images (both `↦ 1`), while the
    count reading `Raw.value` — which uses the distinguishing through `+` — *separates* them
    (`5 ≠ 4`).  So a reading blind to the act cannot carry the prime/composite distinction the FTA
    rests on: the distinguishing is necessary, not decorative. -/
theorem factorization_forced_by_distinguishing :
    (Irreducible Nat213.five ∧ ¬ Irreducible Nat213.four)
    ∧ (Generation.degLens.view (Bridge.toRaw Nat213.four)
        = Generation.degLens.view (Bridge.toRaw Nat213.five))
    ∧ (Raw.value (Bridge.toRaw Nat213.four)
        ≠ Raw.value (Bridge.toRaw Nat213.five)) := by
  refine ⟨⟨five_irreducible, four_not_irreducible⟩, ?_, ?_⟩
  · rw [blind_collapses, blind_collapses]
  · rw [Bridge.value_toRaw, Bridge.value_toRaw]; decide

/-! ## M6 — the schema-level dichotomy (every rival `≅ Raw`, or fails a named clause)

The forcing of M5 was a *single* blind reading (`degLens`).  Here it is lifted to the schema level:
every candidate carrier sits on one of two sides of `UniversalDistinguishing.DStr`.  **Honest status**:
the *positive* arm — a `Generated` `DStr` is `≅ Raw`, hence carries the FTA by transport — needs the
**open** `DStr` existence leg (the `the_distinguishing_schema` frontier; only the
uniqueness half `dhom_unique_pointwise` is proven).  The *negative* arm is closed here, schema-level. -/

open E213.Lens.Foundations.UniversalDistinguishing (DStr Generated rawDStr rawDStr_generated
  no_DStr_on_subsingleton)

/-- `four ≠ five` in the FTA carrier — the prime/composite distinction the FTA rests on. -/
theorem four_ne_five : Nat213.four ≠ Nat213.five := by decide

/-- ★★ **A distinguishing-blind (subsingleton) carrier cannot host the FTA carrier** — no injection
    `Nat213 ↪ α` exists, because `four ≠ five` would have to collapse.  This lifts M5's single
    `degLens` instance to *every* degenerate rival: a carrier that draws no distinction cannot even
    embed the carrier the FTA lives on. -/
theorem subsingleton_cannot_host_fta {α : Type} (hsub : ∀ x y : α, x = y) :
    ¬ ∃ f : Nat213 → α, ∀ m n, f m = f n → m = n := by
  rintro ⟨f, hinj⟩
  exact four_ne_five (hinj _ _ (hsub (f Nat213.four) (f Nat213.five)))

/-- ★★★ **The forcing dichotomy (negative arm closed, positive arm = the open existence leg).**
    *Positive side*: the FTA carrier's home `Raw` is the free distinguishing-structure
    (`rawDStr` is `Generated`), and the FTA carrier `Nat213` embeds into it injectively
    (`Bridge.toRaw_injective`).  *Negative side*: any distinguishing-blind (subsingleton) carrier
    neither hosts the FTA carrier (`subsingleton_cannot_host_fta`) nor is even a `DStr` — it fails the
    *named* clause D1 `e_ne` (`no_DStr_on_subsingleton`).  The remaining gap — that *every* `Generated`
    `DStr` is `≅ Raw` and so carries the FTA by transport — is the open `DStr` existence leg, recorded
    honestly, not claimed. -/
theorem forcing_dichotomy :
    (Generated rawDStr
      ∧ (∀ m n : Nat213, Bridge.toRaw m = Bridge.toRaw n → m = n))
    ∧ (∀ {α : Type}, (∀ x y : α, x = y) →
         (¬ ∃ f : Nat213 → α, ∀ m n, f m = f n → m = n)
         ∧ ¬ Nonempty (DStr α)) :=
  ⟨⟨rawDStr_generated, fun _ _ h => Bridge.toRaw_injective h⟩,
   fun hsub => ⟨subsingleton_cannot_host_fta hsub, no_DStr_on_subsingleton hsub⟩⟩

end E213.Lens.Number.Nat213.Forcing
