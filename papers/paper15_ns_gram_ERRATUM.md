# Paper 15 Erratum

## Error

The estimate in Lemma 3.1 is incorrect.

What was claimed:
```
Σ_{k+p=q} |k||p| a_k a_p a_q
≤ (Σ|k|²a_k²)^{1/2} (Σa_p²)^{1/2} (Σa_q²)^{1/2}
= Ω^{1/2} · E₀
```

Error: the constraint k+p=q (convolution constraint) means
the three sums are not independent. CS cannot be applied to independent sums.

## Correct estimate

Standard (Ladyzhenskaya):
```
|S| ≤ C ‖ω‖³_{L³} ≤ C Ω^{3/4} P^{3/4}
```

Gram-corrected:
```
|S| ≤ C √d · Ω^{3/4} P^{3/4}
```

Exponent: Ω^{3/4} P^{3/4}, not Ω^{1/2}.

## Consequence

d/dt Ω ≤ -2νP + C√d · Ω^{3/4} P^{3/4}
Young: ≤ -νP + C'd · Ω³/ν³

This is a **cubic ODE**. Not linear growth.
Ω³ allows finite-time blow-up.
NS regularity is not proved.

## What Gram contributes (honest)

Changed: constant is N-dependent → d-dependent (√d = √5).
Unchanged: exponent. Ω^{3/4}P^{3/4}. This is the true barrier of NS.

## 213 analysis

213 interpretation of the error:
Read 23 (entanglement, convolution) as 213 (independent, separated).
Inserted boundary (1) where it should not go.
p, q, k are entangled by k+p=q, but were treated as independent.

Honest cost:
```
|S| ≤ C√d · Ω^{3/4} P^{3/4}

Exponent 3/4 + 3/4 = 3/2 > 1.
Cost 3/2 > 1 = e₁.
```

This excess (3/2 - 1 = 1/2) is the true gap of NS.
Not a 213 budget (5) problem but an **exponent structure** problem.
