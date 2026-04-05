import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)

theorem rightHomologyIso_hom_naturality :
    S₁.rightHomologyIso.hom ≫ CategoryTheory.ShortComplex.homologyMap φ =
      rightHomologyMap φ ≫ S₂.rightHomologyIso.hom := by
  simpa only [CategoryTheory.ShortComplex.RightHomologyData.homologyIso_rightHomologyData, Iso.symm_inv] using
    CategoryTheory.ShortComplex.RightHomologyData.rightHomologyIso_inv_naturality φ S₁.rightHomologyData S₂.rightHomologyData

