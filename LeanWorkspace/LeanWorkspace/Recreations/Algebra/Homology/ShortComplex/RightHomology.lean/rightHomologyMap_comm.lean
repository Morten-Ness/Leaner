import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

theorem rightHomologyMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    CategoryTheory.ShortComplex.rightHomologyMap φ ≫ h₂.rightHomologyIso.hom = h₁.rightHomologyIso.hom ≫ γ.φH := by
  simp only [γ.rightHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

