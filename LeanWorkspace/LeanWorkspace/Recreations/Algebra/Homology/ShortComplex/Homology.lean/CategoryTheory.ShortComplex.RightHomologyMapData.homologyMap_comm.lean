import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂) [S₁.HasHomology] [S₂.HasHomology]

theorem homologyMap_comm :
    CategoryTheory.ShortComplex.homologyMap φ ≫ h₂.homologyIso.hom = h₁.homologyIso.hom ≫ γ.φH := by
  simp only [γ.homologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

