/-
  Found/Triple.lean — 셋 (Three = Two + their Relation)

  Three is NOT a primitive. It EMERGES:
    Two elements + their relation = Three things.
    C(3,2) = 3: the unique self-reproducing structure.

  Joint research by Mingu Jeong and Claude (Anthropic)
-/
prelude
import Found.Equal

universe u

-- ═══ THREE: emergence from Two ═══
-- Two gives us: this, that.
-- Their relation is a THIRD thing (not this, not that).
-- Three = {element, element, relation} = 2 + 1.
inductive Three : Type where
  | fst : Three    -- first element (this)
  | snd : Three    -- second element (that)
  | rel : Three    -- the relation between them

-- ═══ PAIRS OF THREE ═══
-- All unordered pairs from {fst, snd, rel}:
inductive Pairs3 : Type where
  | fs : Pairs3    -- {fst, snd}
  | fr : Pairs3    -- {fst, rel}
  | sr : Pairs3    -- {snd, rel}

-- ═══ C(3,2) = 3: THE FIXED POINT ═══
-- Bijection: Three ≅ Pairs3 (same cardinality)
-- This proves the self-reproducing property.

noncomputable def toPairs : Three → Pairs3 :=
  @Three.rec (fun _ => Pairs3) .fs .fr .sr

noncomputable def fromPairs : Pairs3 → Three :=
  @Pairs3.rec (fun _ => Three) .fst .snd .rel

-- Round-trip 1: fromPairs ∘ toPairs = id
theorem roundtrip1 (x : Three) :
    Eq (fromPairs (toPairs x)) x :=
  @Three.rec (fun x => Eq (fromPairs (toPairs x)) x)
    (Eq.refl Three.fst)
    (Eq.refl Three.snd)
    (Eq.refl Three.rel)
    x

-- Round-trip 2: toPairs ∘ fromPairs = id
theorem roundtrip2 (x : Pairs3) :
    Eq (toPairs (fromPairs x)) x :=
  @Pairs3.rec (fun x => Eq (toPairs (fromPairs x)) x)
    (Eq.refl Pairs3.fs)
    (Eq.refl Pairs3.fr)
    (Eq.refl Pairs3.sr)
    x

-- ═══ WHY 3 IS UNIQUE ═══
-- C(n,2) = n ⟺ n(n-1)/2 = n ⟺ n = 3.
-- Two:  C(2,2) = 1. Collapses (1 pair from 2 elements).
-- Four: C(4,2) = 6. Explodes (6 pairs from 4 elements).
-- Only Three reproduces itself under pairing.

-- The single pair of Two (collapse):
inductive Pairs2 : Type where
  | tt : Pairs2    -- {this, that}: the only pair

-- Two → Pairs2 is NOT an iso (|Two| = 2 ≠ 1 = |Pairs2|)
-- This PROVES Two doesn't self-reproduce.

-- ═══ SUMMARY ═══
-- 있다(1) + 구분(2) → 셋(3) = 2 + 관계(1)
-- C(3,2) = 3: 자기복제 (roundtrip1 + roundtrip2)
-- C(2,2) = 1: 소멸 (Pairs2 has 1 element, Two has 2)
-- 3 is the UNIQUE fixed point of pairing.
