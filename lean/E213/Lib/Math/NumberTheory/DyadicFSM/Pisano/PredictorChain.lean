import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModLarge
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModMedium
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.NumberTheory.DyadicFSM.Legendre
import E213.Lib.Math.NumberTheory.DyadicFSM.Pisano.Predictor

/-!
# Pisano predictor chain — per-prime verification, 23 primes

A single file consolidating the per-prime Pisano-predictor
verifications for the Pell-5 trajectory.  Each prime `p` gets
one named lemma `pisano_at_<p>` of the form

```
∀ k, pellFSMmod<p>.bits (k + pisano_predict p _) = pellFSMmod<p>.bits k
```

The proof in every case is

```
pisano_period_lift (by decide) pellFSMmod<p>_bits_period_<X>
```

with `<X>` the predictor-computed period.  Two convenience
conjunctions follow: `pisano_predict_realises_pell_7` (the
7-prime milestone consumed by `NumberTheory213`,
`TwoLayerPredictor`, `SignaturePredict`) and
`pisano_predict_realises_pell_23` (the headline 23-prime
statement).

  | p   | Legendre | branch    | predict | true period | match     |
  |  3  |  2 (NQR) | inert     |    4    |      4      | tight     |
  |  5  |  0       | ramified  |   10    |     10      | tight     |
  |  7  |  2 (NQR) | inert     |    8    |      8      | tight     |
  | 11  |  1 (QR)  | split     |    5    |      5      | tight     |
  | 13  |  2 (NQR) | inert     |   14    |     14      | tight     |
  | 17  |  2 (NQR) | inert     |   18    |     18      | tight     |
  | 19  |  1 (QR)  | split     |    9    |      9      | tight     |
  | 23  |  2 (NQR) | inert     |   24    |     24      | tight     |
  | 29  |  1 (QR)  | split     |   14    |      7      | ×2 sub    |
  | 31  |  1 (QR)  | split     |   15    |     15      | tight     |
  | 37  |  2 (NQR) | inert     |   38    |     38      | tight     |
  | 41  |  1 (QR)  | split     |   20    |     20      | tight     |
  | 43  |  2 (NQR) | inert     |   44    |     44      | tight     |
  | 47  |  2 (NQR) | inert     |   48    |     16      | ×3 sub    |
  | 53  |  2 (NQR) | inert     |   54    |     54      | tight     |
  | 59  |  1 (QR)  | split     |   29    |     29      | tight     |
  | 61  |  1 (QR)  | split     |   30    |     30      | tight     |
  | 67  |  2 (NQR) | inert     |   68    |     68      | tight     |
  | 71  |  1 (QR)  | split     |   35    |     35      | tight     |
  | 73  |  2 (NQR) | inert     |   74    |     74      | tight     |
  | 79  |  1 (QR)  | split     |   39    |     39      | tight     |
  | 89  |  1 (QR)  | split     |   44    |     22      | ×2 sub    |
  | 101 |  1 (QR)  | split     |   50    |     25      | ×2 sub    |

23 of 23 primes verified.  Four sub-tight cases (29, 47, 89, 101)
where the predicted period is a multiple (×2 or ×3) of the true
period — predictor gives an upper bound; tightness analysis is a
separate sub-direction.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Pisano.PredictorChain

open E213.Lib.Math.NumberTheory.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
  (pellFSMmod3 pellFSMmod3_bits_period_4)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod5
  (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod7
  (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod11
  (pellFSMmod11 pellFSMmod11_bits_period_5)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod13
  (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod17
  (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod19
  (pellFSMmod19 pellFSMmod19_bits_period_9)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod23
  (pellFSMmod23 pellFSMmod23_bits_period_24)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod29
  (pellFSMmod29 pellFSMmod29_bits_period_14)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod31
  (pellFSMmod31 pellFSMmod31_bits_period_15)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod37
  (pellFSMmod37 pellFSMmod37_bits_period_38)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod41
  (pellFSMmod41 pellFSMmod41_bits_period_20)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod43
  (pellFSMmod43 pellFSMmod43_bits_period_44)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod47
  (pellFSMmod47 pellFSMmod47_bits_period_48)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod53
  (pellFSMmod53 pellFSMmod53_bits_period_54)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod59
  (pellFSMmod59 pellFSMmod59_bits_period_29)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod61
  (pellFSMmod61 pellFSMmod61_bits_period_30)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod67
  (pellFSMmod67 pellFSMmod67_bits_period_68)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod71
  (pellFSMmod71 pellFSMmod71_bits_period_35)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod73
  (pellFSMmod73 pellFSMmod73_bits_period_74)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod79
  (pellFSMmod79 pellFSMmod79_bits_period_39)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod89
  (pellFSMmod89 pellFSMmod89_bits_period_44)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod101
  (pellFSMmod101 pellFSMmod101_bits_period_50)
open E213.Lib.Math.NumberTheory.DyadicFSM.Pisano.Predictor
  (pisano_predict pisano_period_lift)

/-! ### §1 — Per-prime predictor realisations (23 primes) -/

theorem pisano_at_3 : ∀ k,
    pellFSMmod3.bits (k + pisano_predict 3 (by decide)) = pellFSMmod3.bits k :=
  pisano_period_lift (by decide) pellFSMmod3_bits_period_4

theorem pisano_at_5 : ∀ k,
    pellFSMmod5.bits (k + pisano_predict 5 (by decide)) = pellFSMmod5.bits k :=
  pisano_period_lift (by decide) pellFSMmod5_bits_period_10

theorem pisano_at_7 : ∀ k,
    pellFSMmod7.bits (k + pisano_predict 7 (by decide)) = pellFSMmod7.bits k :=
  pisano_period_lift (by decide) pellFSMmod7_bits_period_8

theorem pisano_at_11 : ∀ k,
    pellFSMmod11.bits (k + pisano_predict 11 (by decide)) = pellFSMmod11.bits k :=
  pisano_period_lift (by decide) pellFSMmod11_bits_period_5

theorem pisano_at_13 : ∀ k,
    pellFSMmod13.bits (k + pisano_predict 13 (by decide)) = pellFSMmod13.bits k :=
  pisano_period_lift (by decide) pellFSMmod13_bits_period_14

theorem pisano_at_17 : ∀ k,
    pellFSMmod17.bits (k + pisano_predict 17 (by decide)) = pellFSMmod17.bits k :=
  pisano_period_lift (by decide) pellFSMmod17_bits_period_18

theorem pisano_at_19 : ∀ k,
    pellFSMmod19.bits (k + pisano_predict 19 (by decide)) = pellFSMmod19.bits k :=
  pisano_period_lift (by decide) pellFSMmod19_bits_period_9

theorem pisano_at_23 : ∀ k,
    pellFSMmod23.bits (k + pisano_predict 23 (by decide)) = pellFSMmod23.bits k :=
  pisano_period_lift (by decide) pellFSMmod23_bits_period_24

theorem pisano_at_29 : ∀ k,
    pellFSMmod29.bits (k + pisano_predict 29 (by decide)) = pellFSMmod29.bits k :=
  pisano_period_lift (by decide) pellFSMmod29_bits_period_14

theorem pisano_at_31 : ∀ k,
    pellFSMmod31.bits (k + pisano_predict 31 (by decide)) = pellFSMmod31.bits k :=
  pisano_period_lift (by decide) pellFSMmod31_bits_period_15

theorem pisano_at_37 : ∀ k,
    pellFSMmod37.bits (k + pisano_predict 37 (by decide)) = pellFSMmod37.bits k :=
  pisano_period_lift (by decide) pellFSMmod37_bits_period_38

theorem pisano_at_41 : ∀ k,
    pellFSMmod41.bits (k + pisano_predict 41 (by decide)) = pellFSMmod41.bits k :=
  pisano_period_lift (by decide) pellFSMmod41_bits_period_20

theorem pisano_at_43 : ∀ k,
    pellFSMmod43.bits (k + pisano_predict 43 (by decide)) = pellFSMmod43.bits k :=
  pisano_period_lift (by decide) pellFSMmod43_bits_period_44

theorem pisano_at_47 : ∀ k,
    pellFSMmod47.bits (k + pisano_predict 47 (by decide)) = pellFSMmod47.bits k :=
  pisano_period_lift (by decide) pellFSMmod47_bits_period_48

theorem pisano_at_53 : ∀ k,
    pellFSMmod53.bits (k + pisano_predict 53 (by decide)) = pellFSMmod53.bits k :=
  pisano_period_lift (by decide) pellFSMmod53_bits_period_54

theorem pisano_at_59 : ∀ k,
    pellFSMmod59.bits (k + pisano_predict 59 (by decide)) = pellFSMmod59.bits k :=
  pisano_period_lift (by decide) pellFSMmod59_bits_period_29

theorem pisano_at_61 : ∀ k,
    pellFSMmod61.bits (k + pisano_predict 61 (by decide)) = pellFSMmod61.bits k :=
  pisano_period_lift (by decide) pellFSMmod61_bits_period_30

theorem pisano_at_67 : ∀ k,
    pellFSMmod67.bits (k + pisano_predict 67 (by decide)) = pellFSMmod67.bits k :=
  pisano_period_lift (by decide) pellFSMmod67_bits_period_68

theorem pisano_at_71 : ∀ k,
    pellFSMmod71.bits (k + pisano_predict 71 (by decide)) = pellFSMmod71.bits k :=
  pisano_period_lift (by decide) pellFSMmod71_bits_period_35

theorem pisano_at_73 : ∀ k,
    pellFSMmod73.bits (k + pisano_predict 73 (by decide)) = pellFSMmod73.bits k :=
  pisano_period_lift (by decide) pellFSMmod73_bits_period_74

theorem pisano_at_79 : ∀ k,
    pellFSMmod79.bits (k + pisano_predict 79 (by decide)) = pellFSMmod79.bits k :=
  pisano_period_lift (by decide) pellFSMmod79_bits_period_39

theorem pisano_at_89 : ∀ k,
    pellFSMmod89.bits (k + pisano_predict 89 (by decide)) = pellFSMmod89.bits k :=
  pisano_period_lift (by decide) pellFSMmod89_bits_period_44

theorem pisano_at_101 : ∀ k,
    pellFSMmod101.bits (k + pisano_predict 101 (by decide)) = pellFSMmod101.bits k :=
  pisano_period_lift (by decide) pellFSMmod101_bits_period_50

/-! ### §2 — Convenience conjunctions

`pisano_predict_realises_pell_7` is the 7-prime milestone
consumed by downstream `NumberTheory213`, `TwoLayerPredictor`,
and `SignaturePredict`.  `pisano_predict_realises_pell_23` is
the headline 23-prime statement.
-/

/-- The 7-prime predictor realisation, packaged as a single
    conjunction for downstream consumers. -/
theorem pisano_predict_realises_pell_7 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide)) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide)) = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide)) = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide)) = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide)) = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide)) = pellFSMmod17.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide)) = pellFSMmod19.bits k) :=
  ⟨pisano_at_3, pisano_at_5, pisano_at_7, pisano_at_11,
   pisano_at_13, pisano_at_17, pisano_at_19⟩

/-- The headline 23-prime predictor realisation. -/
theorem pisano_predict_realises_pell_23 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide)) = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide)) = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide)) = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide)) = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide)) = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide)) = pellFSMmod17.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide)) = pellFSMmod19.bits k)
    ∧ (∀ k, pellFSMmod23.bits (k + pisano_predict 23 (by decide)) = pellFSMmod23.bits k)
    ∧ (∀ k, pellFSMmod29.bits (k + pisano_predict 29 (by decide)) = pellFSMmod29.bits k)
    ∧ (∀ k, pellFSMmod31.bits (k + pisano_predict 31 (by decide)) = pellFSMmod31.bits k)
    ∧ (∀ k, pellFSMmod37.bits (k + pisano_predict 37 (by decide)) = pellFSMmod37.bits k)
    ∧ (∀ k, pellFSMmod41.bits (k + pisano_predict 41 (by decide)) = pellFSMmod41.bits k)
    ∧ (∀ k, pellFSMmod43.bits (k + pisano_predict 43 (by decide)) = pellFSMmod43.bits k)
    ∧ (∀ k, pellFSMmod47.bits (k + pisano_predict 47 (by decide)) = pellFSMmod47.bits k)
    ∧ (∀ k, pellFSMmod53.bits (k + pisano_predict 53 (by decide)) = pellFSMmod53.bits k)
    ∧ (∀ k, pellFSMmod59.bits (k + pisano_predict 59 (by decide)) = pellFSMmod59.bits k)
    ∧ (∀ k, pellFSMmod61.bits (k + pisano_predict 61 (by decide)) = pellFSMmod61.bits k)
    ∧ (∀ k, pellFSMmod67.bits (k + pisano_predict 67 (by decide)) = pellFSMmod67.bits k)
    ∧ (∀ k, pellFSMmod71.bits (k + pisano_predict 71 (by decide)) = pellFSMmod71.bits k)
    ∧ (∀ k, pellFSMmod73.bits (k + pisano_predict 73 (by decide)) = pellFSMmod73.bits k)
    ∧ (∀ k, pellFSMmod79.bits (k + pisano_predict 79 (by decide)) = pellFSMmod79.bits k)
    ∧ (∀ k, pellFSMmod89.bits (k + pisano_predict 89 (by decide)) = pellFSMmod89.bits k)
    ∧ (∀ k, pellFSMmod101.bits (k + pisano_predict 101 (by decide)) = pellFSMmod101.bits k) :=
  ⟨pisano_at_3, pisano_at_5, pisano_at_7, pisano_at_11, pisano_at_13,
   pisano_at_17, pisano_at_19, pisano_at_23, pisano_at_29, pisano_at_31,
   pisano_at_37, pisano_at_41, pisano_at_43, pisano_at_47, pisano_at_53,
   pisano_at_59, pisano_at_61, pisano_at_67, pisano_at_71, pisano_at_73,
   pisano_at_79, pisano_at_89, pisano_at_101⟩

end E213.Lib.Math.NumberTheory.DyadicFSM.Pisano.PredictorChain
