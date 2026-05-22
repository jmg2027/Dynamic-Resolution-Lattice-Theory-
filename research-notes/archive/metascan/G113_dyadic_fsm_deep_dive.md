# G113 — DyadicFSM Tier-2/3 deep dive (1,272 decls — biggest single subtree)

**Date**: 2026-05-22  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Predecessor**: G108 (Real213/Analysis), G110 (FluxMVT),
G111 (Cohomology), G112 (HodgeConjecture).  
**Context**: After Math.Cohomology and Math.HodgeConjecture,
DyadicFSM is the next-largest unexplored subtree.  At 1,272
decls it's actually the **single biggest subtree** in
Lib/Math.

---

## §1.  Scale + distribution

**1,272 decls** — largest single Math subtree in the corpus.
Distribution:

| Sub-area | decls | Role |
|----------|------:|------|
| **ArithFSM**    | **622** | Multi-state arithmetic FSM family (Pell-like sequences) |
| **Fib**         | **159** | Fibonacci-FSM mod-p variants + Pisano relation |
| Signature       |  79 | Signature predictor + classifier + conjecture |
| Trib            |  61 | Tribonacci variants + CRT4Capstone |
| Pell            |  58 | Pell equation cluster |
| BitAuto2        |  46 | 2-state bit automaton |
| BitFSM          |  44 | Bool-pred bit-FSM |
| Product         |  39 | Product FSM (LCM closure, ProductFSMPeriod) |
| Archive         |  31 | Historical (EdgeSignature, SubwordComplexity) |
| Pisano          |  28 | Pisano-period predictor per base |
| Legendre        |  27 | Legendre-symbol Pisano |
| Forward         |  23 | Forward closure/eventual/periodicity |
| Tier            |  20 | AlgebraicDegree / Tier2Hardness / TierBridge |
| LucasFSMmod5    |  19 | Lucas-FSM mod 5 |
| ThueMorse       |   7 | Thue-Morse master |
| ConcretePellSig |   5 | Concrete Pell signature |

**ArithFSM dominates** (49 % of decls).  Then Fib (12.5 %).
The two together: 61 % of DyadicFSM.

### Important: 0 Raw, 0 Lens, 0 Cochain

DyadicFSM has **0 direct Raw/Lens/Cochain/Cut touches** in any
of its 1,272 decls.  Pure Nat / Fin / Bool / List / Decidable
machinery.  **Most extreme Tier-3 encapsulation** (G108
classification).

But its content IS Raw-derived through atomicity numerics —
the moduli used (3, 5, 7, 11, 13, 17, 19, 23, 29, ...) and the
Pell-sequence structure derive from Mobius213 / atomicity chain.

---

## §2.  Architecture

```
                  Atomicity output: (NS=3, NT=2, d=5)
                       ↓ (via Mobius213 P matrix)
                  Pell unit invariant: P^N ≡ I (mod p)
                       ↓
              Pell sequence (a_{k+1}, b_{k+1}) = (2a+b, a+b)
                       ↓
                  ArithFSM2 carrier:
                  structure ArithFSM2 (n : Nat) where
                    init : Fin n × Fin n
                    step : Fin n × Fin n → Fin n × Fin n
                    out  : Fin n × Fin n → Bool
                       ↓
              Per-modulus instances (pellFSMmod3, mod5, mod7, ...)
                       ↓
              Run period theorems (period_24 mod 11, period_28 mod 13, ...)
                       ↓
         Pisano predictor (pisano_predict_realises_pell_N)
                       ↓
         Fib/Trib/Legendre/Lucas variants
                       ↓
              Signature framework
              (Signature, SignatureBipartite, SignaturePredict)
                       ↓
            Forward closure: eventual periodicity proofs
                       ↓
              Product FSM (LCM closure, product period)
                       ↓
              Tier classification (Tier2Hardness, AlgebraicDegree)
                       ↓
              ThueMorse master
```

---

## §3.  The ArithFSM2 carrier — Pell-like FSMs

```lean
structure ArithFSM2 (n : Nat) where
  init : Fin n × Fin n
  step : Fin n × Fin n → Fin n × Fin n
  out  : Fin n × Fin n → Bool

def ArithFSM2.run {n} (m : ArithFSM2 n) : Nat → Fin n × Fin n
  | 0 => m.init
  | k+1 => m.step (m.run k)

def ArithFSM2.bits {n} (m : ArithFSM2 n) (k : Nat) : Bool :=
  m.out (m.run k)
```

**Joint state space**: Fin n × Fin n = n² values.  Transitions
are arithmetic recurrences (matrix mod n).

For Pell (√2): `(a_{k+1}, b_{k+1}) = (2a+b, a+b)` has finite
state mod any N.  This makes Pell sequences **automaton-
analysable** at any modulus.

### Templated family pattern

**457 pellFSMmod* decls**, **145 fibFSMmod* decls**, **45
pisano* decls** — three massive templated families.  Each
modulus p ∈ {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, ...}
gets its own instance with periodicity proof.

This is the **Pattern #2 universal at maximum scale** — same
structural recursion + decide-base, instantiated 457+ times.

---

## §4.  Heavy proof clusters

### Cluster I — Pisano predictor master theorems

  · `Pisano.Predictor17.pisano_predict_realises_pell_17`: **226,403 nodes**
  · `Pisano.Predictor14.pisano_predict_realises_pell_14`: 124,061
  · `Pisano.Predictor11.pisano_predict_realises_pell_11`: 59,142
  · `Pisano.Predictor8.pisano_predict_realises_pell_8`: 34,384
  · `Pisano.Predictor7.pisano_predict_realises_pell_7`: 24,630
  · `Pisano.Predictor6.pisano_predict_realises_pell_6`: 20,433

**Pisano predictor scales with modulus**: predictor_N's mass
roughly follows the Pisano period at base N.  Predictor17 is
the heaviest single non-Cup/AW proof in the corpus
(226K nodes).

### Cluster II — ThueMorse master

  · `ThueMorse.thueMorse_master`: 65,979 nodes

Single-file capstone tying Thue-Morse sequence to the DyadicFSM
framework.

### Cluster III — Signature predictor + Forward eventual periodicity

  · `SignaturePredict.signature_predict_realises_pell_7`: 31,180
  · `Fib.Pisano8.fib_pisano_predict_realises_8`: 23,971
  · `BitFSM.Bound.fsm_signature_period_bound`: 18,399
  · `ArithFSM.V3Equiv.toBitFSM3_run_encode`: 17,338
  · `Forward.ForwardEventual.signature_eventually_periodic_of_eventually_periodic_bits`: 14,697

Plus per-mod `pellFSMmod*_run_period_*` proofs — likely many
in the 1-10K node range each, totaling massive aggregate mass.

---

## §5.  Pattern #2 universal at DyadicFSM scale

G90 M3 surfaced 8 `pellProperModN_run_period_*` decls sharing
recursor op-multiset.  G91 §"Top tactic-sequence clusters"
identified 37 decls matching `[intro, induction, decide, show,
rw]` template — the Pell-FSM template.

**G113 reveals the full scale**: 457 pellFSMmod* decls, 145
fibFSMmod*, 45 pisano* — over **650 decls** following Pattern
#2 universal structure within DyadicFSM alone.

This is **the single largest empirical demonstration of
Pattern #2 in the corpus**.  Each instance:
  1. Construct an ArithFSM2 / BitFSM at modulus p
  2. Prove `run_period = π(p)` (Pisano period) by induction +
     decide-base
  3. Conclude `bits eventually periodic with period π(p)`

The pattern is parametric over `p`, the modulus — perfect
abstraction candidate (FSM-RES1 below).

---

## §6.  Action items from G113

### FSM-1 — pellFSMmod* parametric (457 sites!)

457 per-mod Pell-FSM decls share Pattern #2 structure.
Parametric form:
```lean
theorem pellFSMmod_period (p : Nat) (h_prime_or_atom : ...)
    (period : Nat) (h_witness : period = pisanoPeriod p) :
    ∀ k, (pellFSMmod p).bits (k + period) =
         (pellFSMmod p).bits k
```

**Mass reduction**: largest abstraction candidate in the
corpus.  Likely retires hundreds of thousands of Expr nodes if
all 457 sites collapse to one parametric.

**Effort**: large marathon (5-10 sessions).  Requires
formalising `pisanoPeriod : Nat → Nat` as a Pisano period
function + proving the parametric statement.  Complex but
highest single mass-reduction potential.

### FSM-2 — fibFSMmod* parametric (145 sites)

Same shape for Fibonacci-FSM family.  145 per-mod decls.

**Effort**: medium marathon (3-5 sessions), parallel to FSM-1.

### FSM-3 — pisano* predictor master pattern

`pisano_predict_realises_pell_N` for N ∈ {6, 7, 8, 11, 14, 17}.
6 byte-non-identical but structurally similar proofs.
Mass scales with Pisano period at N.

**Effort**: medium marathon (3-5 sessions).  Generic
`pisano_predict_realises_pell_N` template parametric over N.

### FSM-4 — Tribonacci CRT4Capstone family

`Trib/CRT4Capstone.lean` — 4-way CRT closure for Tribonacci.
Likely templated structure (4 mod-instances).

**Effort**: short marathon.

### FSM-5 — Forward closure family

Forward.ForwardClosure / Forward.ForwardEventual /
Forward.ForwardPeriodicity — three forward-closure proofs.
Likely shared template.

**Effort**: short.

---

## §7.  Research questions from G113

### FSM-RES1 — Pisano period function ∀p

Currently each Predictor_N is hand-written.  **Question**: can
the Pisano period `π : Nat → Nat` be defined as a Lean
function with computable closed form for primes (via Legendre
symbol)?  If yes, the entire Predictor family collapses to a
single theorem.

**Effort**: 5-10 sessions.  Requires Legendre-symbol +
quadratic reciprocity infrastructure.  May not be tractable in
DRLT's PURE setting without expanding the math infrastructure.

### FSM-RES2 — Connection to Mobius213 / atomicity

DyadicFSM's modular content (mod 3, mod 5, etc.) connects to
Mobius213's `P^N ≡ -I (mod 5)` headline.  But the connection is
SOCIOLOGICAL — DyadicFSM files don't directly cite Mobius213.

**Question**: can the connection be formalised?  A theorem
`pellFSMmod_p_run_at_d_squared ≡ Mobius213.P_at_d_squared_mod_p`
would tie the FSM framework to the atomicity chain
explicitly.

**Effort**: 2-3 sessions.

### FSM-RES3 — Signature bipartite ↔ K_{NS,NT} bipartite

`Signature/SignatureBipartite.lean` — signature framework
bipartite structure.  G109 CDI-1 anchors at K_{NS,NT}
bipartite Betti number.

**Question**: is SignatureBipartite formally connected to
K_{NS,NT}^{(c)}'s bipartite structure?  This would be a
DyadicFSM → Cohomology bridge.

**Effort**: 2-3 sessions.

### FSM-RES4 — Tier hardness theory + algebraic degree

`Tier/AlgebraicDegree.lean`, `Tier/Tier2Hardness.lean`,
`Tier/TierBridge.lean` — tier classification of FSMs by
algebraic degree.

**Question**: does this give DRLT a hardness-of-decision
result analogous to Turing machine theory?  Linkage to
G115 Bishop comparison?

**Effort**: research-level, possibly multi-session.

---

## §8.  Significance for the meta-scan tree

### What G113 confirms

  · **Pattern #2 universal at extreme scale**: 650+ decls
    follow the same pellFSMmod/fibFSMmod/pisano template.
    Single biggest scale of Pattern #2 in the corpus.
  · **Tier-3 deep encapsulation**: DyadicFSM is **most
    encapsulated** — 0 direct Raw / Lens / Cochain / Cut
    touches across 1,272 decls.  Pure Nat / Fin / Bool / List
    machinery.  Content connects to Raw via atomicity numerics
    (the moduli are atomicity primes), but the connection is
    type-level + content-level, not Expr-level.
  · **Heaviest single-tactic proof in corpus**: Pisano
    Predictor17 at 226,403 nodes — largest non-CupAW/non-
    LeibnizAlgLift proof.

### What G113 newly surfaces

  · **FSM-1 candidate at 457 sites** — single largest
    parametric abstraction candidate in the corpus.  If
    closed, retires potentially hundreds of thousands of Expr
    nodes.
  · **Hidden Mobius213 ↔ DyadicFSM bridge** (FSM-RES2) — a
    formal connection waiting to be made.
  · **Tier hardness theory** (FSM-RES4) — DRLT-internal
    complexity theory.

### What's still unexplored after G113

  · **CayleyDickson** (629 decls) — algebraic-integer tower.
  · **Lib.Physics subtrees** — covered partially in G109
    cross-domain bridges but not deeply analysed.

---

## §9.  Updated executor priority (G108-G113 consolidated, top 12)

1. **L1 LeibnizAlgLift marathon** (biggest single mass)
2. **G113 FSM-1 pellFSMmod parametric** (457 sites, largest
   abstraction candidate in corpus)
3. **G111 COH-1+COH-2+COH-3 batch** (~90K nodes)
4. **G112 HC-1 capstone-template investigation**
5. **G110 FLUX-1 forward/backward parametric**
6. **G113 FSM-3 pisano_predict_realises_pell template**
7. **G108 REAL-1 + REAL-2** Cut iff consolidation
8. **G113 FSM-2 fibFSMmod parametric** (145 sites)
9. **G108 CutSumOne C template**
10. **G114 CayleyDickson deep dive** (1-2 sessions)
11. **G112 HC-2 per-surface HodgeIndex template**
12. **G115 Bishop comparison** (REAL-RES6)

**Single highest-value abstraction**: G113 FSM-1 (457 sites)
or L1 marathon (6-layer overdetermined, 50% mass cut).

**Doctrinal capstones**: G108 §10 REAL-RES6 (Bishop), G111 §8
COH-RES5 (Pattern #17 framework), G113 FSM-RES2 (Mobius213
bridge), G112 HC-RES2 (bridge unification).

---

## §10.  Artifacts

  · This document: `research-notes/G113_dyadic_fsm_deep_dive.md`
  · Source: G102 callgraph + G103 shape + Lean source
    inspection.

Next Tier candidates: CayleyDickson (G114), Lib.Physics
(G115+), or doctrinal capstones (G116 = Bishop).
