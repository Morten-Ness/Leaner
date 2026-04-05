import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

set_option backward.isDefEq.respectTransparency false in
theorem cyclesMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    CategoryTheory.ShortComplex.cyclesMap φ = h₁.cyclesIso.hom ≫ γ.φK ≫ h₂.cyclesIso.inv := by
  dsimp [LeftHomologyData.cyclesIso, CategoryTheory.ShortComplex.cyclesMapIso']
  rw [← γ.cyclesMap'_eq, ← CategoryTheory.ShortComplex.cyclesMap'_comp, ← CategoryTheory.ShortComplex.cyclesMap'_comp, id_comp, comp_id]
  rfl

