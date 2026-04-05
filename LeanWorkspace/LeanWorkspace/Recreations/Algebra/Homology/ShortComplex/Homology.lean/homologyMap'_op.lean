import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem homologyMap'_op : (CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂).op =
    h₂.iso.inv.op ≫ CategoryTheory.ShortComplex.homologyMap' (opMap φ) h₂.op h₁.op ≫ h₁.iso.hom.op := Quiver.Hom.unop_inj (by
    dsimp
    have γ : HomologyMapData φ h₁ h₂ := default
    simp only [γ.homologyMap'_eq, γ.CategoryTheory.ShortComplex.HomologyMapData.homologyMap'_eq CategoryTheory.ShortComplex.HomologyData.op, HomologyData.op_left,
      HomologyMapData.op_left, RightHomologyMapData.op_φH, Quiver.Hom.unop_op, assoc,
      ← γ.comm_assoc, Iso.hom_inv_id, comp_id])

