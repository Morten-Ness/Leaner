import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

set_option backward.isDefEq.respectTransparency false in
theorem leftHomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    CategoryTheory.ShortComplex.leftHomologyMap φ = h₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv := by
  dsimp [LeftHomologyData.leftHomologyIso, CategoryTheory.ShortComplex.leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq, ← CategoryTheory.ShortComplex.leftHomologyMap'_comp,
    ← CategoryTheory.ShortComplex.leftHomologyMap'_comp, id_comp, comp_id]
  rfl

