import E213.Lib.Math.Combinatorics.BoolEnum
import E213.Lib.Math.Combinatorics.ListCount

/-!
# A concrete connected coboundary: `|im δ⁰| = 2^(V−1)` fully ∅-axiom

`BettiOneUniversal` reads `|im δ⁰| = 2^(V−1)` through a first-isomorphism
bridge whose combinatorial half (`im_dim_via_transversal`) is proven, but
which still *cites* "δ⁰-fiber = `{σ, complement σ}` pair".  That cited
step needs a coboundary map's linearity, which `delta0Tri` (function
valued, `Fin → Bool`) cannot supply for an image *count* without `funext`.

This file removes the citation by working with a **list-valued** connected
coboundary — the path-graph coboundary `pathDelta l = consecutive XORs`.
Its image cardinality is `2^(V−1)`, **fully proven** (no funext, no
Fintype, no division):

  - `pathDelta_complement` — `pathDelta (complement l) = pathDelta l`, so
    each `{σ, complement σ}` pair has a single coboundary (surjectivity
    onto the image from the head-`false` representatives);
  - `pathDelta_reconstruct` — equal length + equal `pathDelta` + equal
    head ⇒ equal list, so `pathDelta` is injective on head-`false`
    colourings;
  - `im_pathDelta_card` — the head-`false` representatives map injectively
    and surjectively onto `im pathDelta`, giving `|im| = 2^(V−1)`.

Since `dim im δ⁰ = V − dim ker δ⁰ = V − 1` is the same for **every**
connected graph on `V` vertices (rank–nullity; `dim ker = 1` is the
connectedness content, proven for `K_{NS,NT}^{(c)}` in
`KernelConstancyUniversal`), this `2^(V−1)` is `|im δ⁰|` for the
complete-bipartite deployment too.  `BettiOneUniversal` then turns it into
`b₁ = E − V + 1`.

Companion: `theory/math/cohomology/bipartite.md`.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.PathCoboundary

open E213.Lib.Math.Combinatorics.BoolEnum
  (allBoolLists headFalse complement bcount bcount_headFalse headFalse_transversal
   length_of_mem_allBoolLists mem_allBoolLists mem_map_of_mem nodup_allBoolLists
   filter_length_eq_bcount)
open E213.Lib.Math.Combinatorics.ListCount
  (nodup_map_of_inj mem_filter mem_filter_of nodup_filter)
open E213.Tactic.List213 (length_map)

/-! ## The path coboundary -/

/-- Path-graph coboundary: the list of consecutive XORs.  `pathDelta` of a
    length-`V` colouring has length `V − 1`. -/
def pathDelta : List Bool → List Bool
  | [] => []
  | [_] => []
  | a :: b :: rest => xor a b :: pathDelta (b :: rest)

/-- `xor` of two negations is the original `xor`. -/
private theorem xor_not_not (a b : Bool) : xor (a == false) (b == false) = xor a b := by
  cases a <;> cases b <;> rfl

/-- **Complement invariance**: flipping every vertex leaves the consecutive
    XORs unchanged.  So `σ` and `complement σ` have the same coboundary. -/
theorem pathDelta_complement : ∀ l, pathDelta (complement l) = pathDelta l
  | [] => rfl
  | [_] => rfl
  | a :: b :: rest => by
      show xor (a == false) (b == false) :: pathDelta (complement (b :: rest))
            = xor a b :: pathDelta (b :: rest)
      rw [xor_not_not, pathDelta_complement (b :: rest)]

/-! ## Reconstruction (injectivity on head-fixed colourings) -/

/-- From `a = c` and `xor a b = xor c d`, conclude `b = d`. -/
private theorem xor_mid_cancel {a b c d : Bool} (hac : a = c)
    (h : xor a b = xor c d) : b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | rfl | exact Bool.noConfusion hac | exact Bool.noConfusion h

/-- A colouring is determined by its head and its consecutive XORs:
    equal length, equal `pathDelta`, equal head ⇒ equal list. -/
theorem pathDelta_reconstruct :
    ∀ {σ τ : List Bool}, σ.length = τ.length → pathDelta σ = pathDelta τ →
      σ.head? = τ.head? → σ = τ
  | [], [], _, _, _ => rfl
  | [a], [c], _, _, hh => by
      have hac : a = c := Option.some.inj hh; rw [hac]
  | a :: b :: s, c :: d :: t, hlen, hpd, hh => by
      have hac : a = c := Option.some.inj hh
      have hpd' : xor a b :: pathDelta (b :: s) = xor c d :: pathDelta (d :: t) := hpd
      have h1 : xor a b = xor c d := by injection hpd'
      have h2 : pathDelta (b :: s) = pathDelta (d :: t) := by injection hpd'
      have hbd : b = d := xor_mid_cancel hac h1
      have hlen' : (b :: s).length = (d :: t).length := Nat.succ.inj hlen
      have htail : (b :: s) = (d :: t) :=
        pathDelta_reconstruct hlen' h2 (congrArg some hbd)
      rw [hac, htail]
  | [], _ :: _, hlen, _, _ => Nat.noConfusion hlen
  | _ :: _, [], hlen, _, _ => Nat.noConfusion hlen
  | [_], _ :: _ :: _, hlen, _, _ => Nat.noConfusion (Nat.succ.inj hlen)
  | _ :: _ :: _, [_], hlen, _, _ => Nat.noConfusion (Nat.succ.inj hlen)

/-! ## Image cardinality -/

/-- A head-`false` colouring has `head? = some false`. -/
private theorem head?_of_headFalse : ∀ {l : List Bool}, headFalse l = true →
    l.head? = some false
  | [], h => Bool.noConfusion h
  | false :: _, _ => rfl
  | true :: _, h => Bool.noConfusion h

/-- `complement` preserves length. -/
private theorem complement_length (l : List Bool) :
    (complement l).length = l.length := length_map l _

/-- ★★★★★★ **`|im pathDelta| = 2^(V−1)` — fully ∅-axiom.**

  The head-`false` colourings of length `n + 1` map under `pathDelta` to a
  list of coboundaries that is `Nodup` (injectivity, via
  `pathDelta_reconstruct`), has length `2^n` (`bcount_headFalse`), and
  contains every coboundary (surjectivity from representatives, via
  `pathDelta_complement` + `headFalse_transversal`).  So the path
  coboundary has exactly `2^n = 2^(V−1)` distinct values — `dim im = V−1`,
  no `funext` / `Fintype` / `Nat.div`. -/
theorem im_pathDelta_card (n : Nat) :
    (((allBoolLists (n + 1)).filter headFalse).map pathDelta).Nodup
    ∧ (((allBoolLists (n + 1)).filter headFalse).map pathDelta).length = 2 ^ n
    ∧ ∀ σ, σ ∈ allBoolLists (n + 1) →
        pathDelta σ ∈ ((allBoolLists (n + 1)).filter headFalse).map pathDelta := by
  refine ⟨?_, ?_, ?_⟩
  · -- Nodup: pathDelta is injective on the head-false representatives
    refine nodup_map_of_inj ?_ (nodup_filter headFalse (nodup_allBoolLists (n + 1)))
    intro σ hσ τ hτ hpd
    exact pathDelta_reconstruct
      ((length_of_mem_allBoolLists (mem_filter hσ).1).trans
        (length_of_mem_allBoolLists (mem_filter hτ).1).symm)
      hpd
      ((head?_of_headFalse (mem_filter hσ).2).trans
        (head?_of_headFalse (mem_filter hτ).2).symm)
  · -- length = 2^n
    rw [length_map, filter_length_eq_bcount, bcount_headFalse]
  · -- surjectivity: every coboundary comes from a head-false representative
    intro σ hσ
    have hσl : σ.length = n + 1 := length_of_mem_allBoolLists hσ
    cases hhf : headFalse σ with
    | true => exact mem_map_of_mem pathDelta (mem_filter_of hσ hhf)
    | false =>
        -- representative is complement σ (head-false), same coboundary
        have hchf : headFalse (complement σ) = true := by
          cases σ with
          | nil => exact Nat.noConfusion hσl
          | cons a l =>
              have ht := headFalse_transversal a l
              rw [hhf] at ht
              cases hc : headFalse (complement (a :: l)) with
              | true => rfl
              | false => rw [hc] at ht; exact Bool.noConfusion ht
        have hcmem : complement σ ∈ allBoolLists (n + 1) := by
          have hl : (complement σ).length = n + 1 := by rw [complement_length, hσl]
          exact hl ▸ mem_allBoolLists (complement σ)
        rw [(pathDelta_complement σ).symm]
        exact mem_map_of_mem pathDelta (mem_filter_of hcmem hchf)

end E213.Lib.Math.Cohomology.Bipartite.Parametric.PathCoboundary
