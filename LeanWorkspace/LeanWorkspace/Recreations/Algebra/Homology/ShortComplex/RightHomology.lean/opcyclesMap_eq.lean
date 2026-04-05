import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

set_option backward.isDefEq.respectTransparency false in
theorem opcyclesMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    CategoryTheory.ShortComplex.opcyclesMap φ = h₁.opcyclesIso.hom ≫ γ.φQ ≫ h₂.opcyclesIso.inv := by
  dsimp [RightHomologyData.opcyclesIso, cyclesMapIso']
  rw [← γ.opcyclesMap'_eq, ← CategoryTheory.ShortComplex.opcyclesMap'_comp, ← CategoryTheory.ShortComplex.opcyclesMap'_comp, id_comp, comp_id]
  rfl

