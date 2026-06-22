# Decomposition: the integers ℤ ("negative numbers")

*213-decomposition of ℤ, per `../README.md`.*

## The decomposition

- **Construction `C`** — a **directed count-pair** `(m, n)`: two counts (each itself iterated
  distinguishing), distinguished from each other *with a direction* (which is the minuend). The
  direction is the new content beyond ℕ — it is one extra distinguishing (a `Bool`-style pair-swap),
  not a new kind of thing.
- **Reading `L₋`** — the **difference-reading** `(m, n) ↦ m − n`. In Lean exactly
  `Nat213.Tower.NatPairToInt.npairToInt (m,n) := Int.subNatNat m n`: ℤ is the *readout* of this Lens,
  magnitude `Nat`-style and sign `Bool`-style (pair-swap).
- **Residue** — the reading is many-to-one (`(m,n)` and `(m+k, n+k)` read the same); the residue is
  the whole anti-diagonal a single integer forgets. "Lowest terms" / `Int.subNatNat` normalizing is
  *applying* the Lens, never the substance.

## Re-seeing

```
   ℤ            =  ⟨ directed count-pair (m,n) | L₋ = (m − n) ⟩
   "−3"         =  L₋ of any (m,n) with n − m = 3      (e.g. (0,3), (1,4), …)
   "the sign"   =  the pair-swap bit of C, read out by L₋ — not a Raw primitive
```

## Revelation (substance/notation collapse caught + forcing)

"Negative number" is **not a new substance** adjoined to ℕ. It is the **difference-reading of a
directed count-pair** — the same counts ℕ already has, distinguished with one extra (direction) bit.
This is exactly the CLAUDE.md failure-mode **"ℤ / sign as exterior import"** stated *positively*: the
miss is treating `−` / sign as a Raw primitive; the decomposition shows it is `L₋` applied to a pair
whose only addition over ℕ is a swap-bit. Lean certifies the readout is faithful and that the two
"directions" are the two sign-cases (`npairToInt`, `subNatNat n 0 = ofNat n`,
`subNatNat 0 n = -(ofNat n)`).

**Forcing**: ℤ is *forced* the moment you ask ℕ's count to be **closed under the difference-reading**
— there is no exterior dialer adding "negatives"; you are reading the *already-present* pair
construction through `L₋`. The subtraction ℕ "cannot do" is not a missing operation but a reading that
needs the pair construction to land.

## Note for the technique

This decomposition argues the README shape-question **"should *direction/order* of distinguishing be a
first-class axis of `C`?"** — *yes*: the sign of ℤ is precisely the direction-bit of `C` surfacing
under `L₋`. The same direction-axis should reappear in orientation, in non-commutativity, and in the
`(m,n)↦m−n` vs `(m,n)↦m/n` (ratio) split that gives ℚ. Candidate: `C` carries an optional
**direction** sub-structure that some readings (difference, ratio) consume and others (count) ignore.
