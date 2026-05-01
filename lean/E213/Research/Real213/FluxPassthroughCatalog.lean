import E213.Research.Real213.FluxPassthroughClass

/-!
# Research.Real213FluxPassthroughCatalog

Phase BK: catalog of Passthrough instances built via combinators.

Demonstrates compositionality: any function buildable from id,
cutPow, ∘, cutMul yields automatic MVT + FTC at unit bracket
through one-liner combinator chains.
-/

namespace E213.Research.Real213.FluxPassthroughCatalog

open E213.Firmware E213.Hypervisor

namespace FluxCut.Passthrough

/-- x ↦ x via id. -/
def x_pass : Passthrough id := id_pass

/-- x ↦ x · x via mul. -/
def square_pass : Passthrough (fun x => cutMul x x) :=
  mul_pass id_pass id_pass

/-- x ↦ x · (x · x) via mul + mul. -/
def cube_pass : Passthrough (fun x => cutMul x (cutMul x x)) :=
  mul_pass id_pass square_pass

/-- x ↦ (x · x) · (x · x) via mul + mul. -/
def quartic_pass :
    Passthrough (fun x => cutMul (cutMul x x) (cutMul x x)) :=
  mul_pass square_pass square_pass

/-- x ↦ (x · x) · (x · x · x) — quintic via mul. -/
def quintic_pass :
    Passthrough (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x))) :=
  mul_pass square_pass cube_pass

/-- x ↦ id ∘ id = id (composition closure check). -/
def id_compose_id_pass : Passthrough (id ∘ id) := compose_pass id_pass id_pass

/-- x ↦ x² ∘ x² = x⁴ via composition (different structure than mul). -/
def square_compose_square_pass :
    Passthrough ((fun x => cutMul x x) ∘ (fun x => cutMul x x)) :=
  compose_pass square_pass square_pass

/-- x ↦ id · x² = x · x² via mul. -/
def id_mul_square_pass :
    Passthrough (fun x => cutMul x (cutMul x x)) :=
  mul_pass id_pass square_pass

/-- ★ Catalog showcase: 7 Passthrough instances all yield MVT auto. -/
theorem catalog_mvt_capstone :
    localDivergence id unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x x) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul x (cutMul x x)) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
        unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence (fun x => cutMul (cutMul x x)
        (cutMul x (cutMul x x))) unitBracket
        = ofCut (constCut 1 1)
    ∧ localDivergence (id ∘ id) unitBracket = ofCut (constCut 1 1)
    ∧ localDivergence ((fun x => cutMul x x) ∘ (fun x => cutMul x x))
        unitBracket = ofCut (constCut 1 1) :=
  ⟨x_pass.mvt, square_pass.mvt, cube_pass.mvt,
   quartic_pass.mvt, quintic_pass.mvt,
   id_compose_id_pass.mvt, square_compose_square_pass.mvt⟩

end FluxCut.Passthrough

end E213.Research.Real213.FluxPassthroughCatalog
