import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

theorem LeftHomologyMapData.quasiIso_iff {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (γ : LeftHomologyMapData φ h₁ h₂) :
    QuasiIso φ ↔ IsIso γ.φH := by
  rw [CategoryTheory.ShortComplex.quasiIso_iff, γ.homologyMap_eq]
  constructor
  · intro h
    haveI : IsIso (γ.φH ≫ (LeftHomologyData.homologyIso h₂).inv) :=
      IsIso.of_isIso_comp_left (LeftHomologyData.homologyIso h₁).hom _
    exact IsIso.of_isIso_comp_right _ (LeftHomologyData.homologyIso h₂).inv
  · intro h
    infer_instance

