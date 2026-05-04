# Pisano marathon — full extraction (26 decls / 9 files)

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor.lean

### \`pisano_predict\` (kind: def)
```lean
def pisano_predict (p : Nat) (hp : 1 < p) : Nat :=
  let leg := (legendre213 5 p hp).val
  if leg = 0 then 2 * p          -- ramified
  else if leg = 1 then (p - 1) / 2  -- split (QR)
  else p + 1                     -- inert (NQR)

/-- ★★★★★★ Predictor matches TIGHT Pell period at all four cases. -/
```

### \`pisano_predict_correct\` (kind: theorem)
```lean
theorem pisano_predict_correct :
    pisano_predict 3 (by decide) = 4
    ∧ pisano_predict 5 (by decide) = 10
    ∧ pisano_predict 7 (by decide) = 8
    ∧ pisano_predict 11 (by decide) = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ The Legendre lens-driven predictor PREDICTS the
    actual Pell bit periods at all four primes — a single
    formula that reads the trajectory and yields the period. -/
```

### \`pisano_predict_realises_pell\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k; rw [pisano_predict_correct.1]; exact pellFSMmod3_bits_period_4 k
  · intro k; rw [pisano_predict_correct.2.1]; exact pellFSMmod5_bits_perio
... [truncated]
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor11.lean

### \`legendre_5_mod_29\` (kind: theorem)
```lean
theorem legendre_5_mod_29 :
    legendre213 5 29 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 31 = QR (split). -/
```

### \`legendre_5_mod_31\` (kind: theorem)
```lean
theorem legendre_5_mod_31 :
    legendre213 5 31 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 37 = NQR (inert). -/
```

### \`legendre_5_mod_37\` (kind: theorem)
```lean
theorem legendre_5_mod_37 :
    legendre213 5 37 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 11 primes.

  Extends the 8-prime evidence (`pisano_predict_realises_pell_8`) by
  adding mod 29, 31, 37.  At each new prime, the Legendre-driven
  predictor formula (split→(p-1)/2, inert→p+1) yields a period N
  satisfying  ∀ k, bits(k + N) = bits(k). -/
```

### \`pisano_predict_realises_pell_11\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell_11 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide))
        = pellFSMm
... [truncated]
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor14.lean

### \`legendre_5_mod_41\` (kind: theorem)
```lean
theorem legendre_5_mod_41 :
    legendre213 5 41 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 43 = NQR (inert). -/
```

### \`legendre_5_mod_43\` (kind: theorem)
```lean
theorem legendre_5_mod_43 :
    legendre213 5 43 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 47 = NQR (inert). -/
```

### \`legendre_5_mod_47\` (kind: theorem)
```lean
theorem legendre_5_mod_47 :
    legendre213 5 47 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 14 primes.

  Extends the 11-prime evidence (`pisano_predict_realises_pell_11`)
  by adding mod 41, 43, 47.  The new phenomenon at p=47:
  predictor formula `p+1=48` gives 3 · tight period (16).
  Predictor still satisfies `bits(k+predict) = bits(k)`.

  Three sub-tight cases now in the table:
    p=29 (split) : predict=14, tight=7  (×2)
    p=47 (inert) : predict=48, tight=16 (×3)  ← NEW

  Generalised conjecture: predictor gives a *Galois orbit* upper

... [truncated]
```

### \`pisano_predict_realises_pell_14\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell_14 :
    -- All 11 previous primes
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (
... [truncated]
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor17.lean

### \`legendre_5_mod_53\` (kind: theorem)
```lean
theorem legendre_5_mod_53 :
    legendre213 5 53 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 59 = QR (split). -/
```

### \`legendre_5_mod_59\` (kind: theorem)
```lean
theorem legendre_5_mod_59 :
    legendre213 5 59 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★ Legendre 5 mod 61 = QR (split). -/
```

### \`legendre_5_mod_61\` (kind: theorem)
```lean
theorem legendre_5_mod_61 :
    legendre213 5 61 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 17 primes. -/
```

### \`pisano_predict_realises_pell_17\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell_17 :
    -- All 14 previous primes
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (
... [truncated]
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor20.lean

### \`legendre_5_mod_67\` (kind: theorem)
```lean
theorem legendre_5_mod_67 :
    legendre213 5 67 (by decide) = ⟨2, by decide⟩ := by decide
```

### \`legendre_5_mod_71\` (kind: theorem)
```lean
theorem legendre_5_mod_71 :
    legendre213 5 71 (by decide) = ⟨1, by decide⟩ := by decide
```

### \`legendre_5_mod_73\` (kind: theorem)
```lean
theorem legendre_5_mod_73 :
    legendre213 5 73 (by decide) = ⟨2, by decide⟩ := by decide
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor22.lean

### \`legendre_5_mod_79\` (kind: theorem)
```lean
theorem legendre_5_mod_79 :
    legendre213 5 79 (by decide) = ⟨1, by decide⟩ := by decide
```

### \`legendre_5_mod_89\` (kind: theorem)
```lean
theorem legendre_5_mod_89 :
    legendre213 5 89 (by decide) = ⟨1, by decide⟩ := by decide
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor6.lean

### \`pisano_predict_correct_6\` (kind: theorem)
```lean
theorem pisano_predict_correct_6 :
    pisano_predict 3 (by decide) = 4
    ∧ pisano_predict 5 (by decide) = 10
    ∧ pisano_predict 7 (by decide) = 8
    ∧ pisano_predict 11 (by decide) = 5
    ∧ pisano_predict 13 (by decide) = 14
    ∧ pisano_predict 19 (by decide) = 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★★★★ Predictor REALISES Pell period at all 6 verified primes. -/
```

### \`pisano_predict_realises_pell_6\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell_6 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod19.bits (k + pisano_predict 19 (by decide))
        = pellFSMmo
... [truncated]
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor7.lean

### \`legendre_5_mod_17\` (kind: theorem)
```lean
theorem legendre_5_mod_17 :
    legendre213 5 17 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Predictor REALISES Pell period at all 7 verified primes. -/
```

### \`pisano_predict_realises_pell_7\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell_7 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide))
        = pellFSMmo
... [truncated]
```

## File: E213/Math/Cohomology/Dyadic/Pisano/Predictor8.lean

### \`legendre_5_mod_23\` (kind: theorem)
```lean
theorem legendre_5_mod_23 :
    legendre213 5 23 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★★★ Bit predictor REALISES Pell period at 8 primes. -/
```

### \`pisano_predict_realises_pell_8\` (kind: theorem)
```lean
theorem pisano_predict_realises_pell_8 :
    (∀ k, pellFSMmod3.bits (k + pisano_predict 3 (by decide))
        = pellFSMmod3.bits k)
    ∧ (∀ k, pellFSMmod5.bits (k + pisano_predict 5 (by decide))
        = pellFSMmod5.bits k)
    ∧ (∀ k, pellFSMmod7.bits (k + pisano_predict 7 (by decide))
        = pellFSMmod7.bits k)
    ∧ (∀ k, pellFSMmod11.bits (k + pisano_predict 11 (by decide))
        = pellFSMmod11.bits k)
    ∧ (∀ k, pellFSMmod13.bits (k + pisano_predict 13 (by decide))
        = pellFSMmod13.bits k)
    ∧ (∀ k, pellFSMmod17.bits (k + pisano_predict 17 (by decide))
        = pellFSMmo
... [truncated]
```
