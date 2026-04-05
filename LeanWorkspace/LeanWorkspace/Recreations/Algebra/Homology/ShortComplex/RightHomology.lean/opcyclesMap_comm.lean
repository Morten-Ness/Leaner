import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

theorem opcyclesMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    CategoryTheory.ShortComplex.opcyclesMap φ ≫ h₂.opcyclesIso.hom = h₁.opcyclesIso.hom ≫ γ.φQ := by
  simp only [γ.opcyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

