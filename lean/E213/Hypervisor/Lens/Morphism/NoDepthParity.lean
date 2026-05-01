import E213.Hypervisor.Lens

/-!
# Research.NoDepthParity: depth parity is not a Lens kernel

**Observation**: the equivalence relation "depth r mod 2" is **not**
a slash-congruence of Raw.  Therefore no Lens can extract depth
parity exactly.

## Reason

`depth(slash x y h) = 1 + max(depth x)(depth y)`.  The parity:

- The parity of max(depth x, depth y) cannot be determined from
  depth x % 2 and depth y % 2 alone.
- Example: (dx=1, dy=2) → max=2 → 1+2=3 odd.
            (dx=3, dy=2) → max=3 → 1+3=4 even.
  The same parity pair (odd, even) yields different result parities.

## Witness

- `rA1`: depth 1 (odd).
- `rA3`: depth 3 (odd).
- `rB2`: depth 2 (even).

- ker_dp(rA1, rA3) (both odd).
- ker_dp(rB2, rB2) (trivial).
- slash(rA1, rB2): depth 1 + max(1, 2) = 3 odd.
- slash(rA3, rB2): depth 1 + max(3, 2) = 4 even.

For ker_dp to be preserved, slash(rA1, rB2) ~ slash(rA3, rB2) would
be required (since rA1~rA3 and rB2~rB2).  But the actual parities
are odd vs even — different.  **Slash-congruence fails.**

Therefore depth parity cannot be extracted by any Lens.
-/

namespace E213.Hypervisor.Lens.Morphism.NoDepthParity

open E213.Firmware E213.Hypervisor

/-- depth 1 witness: `a / b`. -/
def rA1 : Raw := Raw.slash Raw.a Raw.b (by decide)

/-- depth 2 witness: `a / (a/b)`. -/
def rB2 : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-- depth 3 witness: `a / (a / (a/b))`. -/
def rA3 : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

/-- slash (rA1, rB2) has depth 3 (odd). -/
def slash12 : Raw := Raw.slash rA1 rB2 (by decide)

/-- slash (rA3, rB2) has depth 4 (even). -/
def slash32 : Raw := Raw.slash rA3 rB2 (by decide)

theorem rA1_depth_odd : Lens.depth.view rA1 % 2 = 1 := by decide
theorem rA3_depth_odd : Lens.depth.view rA3 % 2 = 1 := by decide
theorem slash12_depth_odd : Lens.depth.view slash12 % 2 = 1 := by decide
theorem slash32_depth_even : Lens.depth.view slash32 % 2 = 0 := by decide

/-- **Depth parity is not a slash-congruence**.  For two depth-odd
    elements (rA1, rA3) and a common rB2, the parity of the slash
    results differs. -/
theorem depth_parity_not_congruence :
    Lens.depth.view rA1 % 2 = Lens.depth.view rA3 % 2 ∧
    Lens.depth.view rB2 % 2 = Lens.depth.view rB2 % 2 ∧
    Lens.depth.view slash12 % 2 ≠ Lens.depth.view slash32 % 2 := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · rfl
  · decide

end E213.Hypervisor.Lens.Morphism.NoDepthParity
