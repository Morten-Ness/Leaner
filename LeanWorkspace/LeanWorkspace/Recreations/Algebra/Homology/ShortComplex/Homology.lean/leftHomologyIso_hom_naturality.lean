import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)

theorem leftHomologyIso_hom_naturality :
    S₁.leftHomologyIso.hom ≫ CategoryTheory.ShortComplex.homologyMap φ =
      leftHomologyMap φ ≫ S₂.leftHomologyIso.hom := by
  simpa only [CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using
    CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_inv_naturality φ S₁.leftHomologyData S₂.leftHomologyData

