import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

set_option backward.isDefEq.respectTransparency false in
theorem rightHomologyMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    CategoryTheory.ShortComplex.rightHomologyMap φ = h₁.rightHomologyIso.hom ≫ γ.φH ≫ h₂.rightHomologyIso.inv := by
  dsimp [RightHomologyData.rightHomologyIso, CategoryTheory.ShortComplex.rightHomologyMapIso']
  rw [← γ.rightHomologyMap'_eq, ← CategoryTheory.ShortComplex.rightHomologyMap'_comp,
    ← CategoryTheory.ShortComplex.rightHomologyMap'_comp, id_comp, comp_id]
  rfl

