import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem RightHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (γ : RightHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [CategoryTheory.ShortComplex.quasiIso_iff, γ.homologyMap_eq]
  constructor
  · intro h
    haveI : IsIso (γ.φH ≫ (RightHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (RightHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (RightHomologyData.homologyIso h₂).inv
  · intro h
    infer_instance

