import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable [S₁.HasHomology] [S₂.HasHomology] (φ : S₁ ⟶ S₂)

theorem leftHomologyIso_inv_naturality :
    S₁.leftHomologyIso.inv ≫ leftHomologyMap φ =
      CategoryTheory.ShortComplex.homologyMap φ ≫ S₂.leftHomologyIso.inv := by
  simpa only [CategoryTheory.ShortComplex.LeftHomologyData.homologyIso_leftHomologyData, Iso.symm_inv] using
    CategoryTheory.ShortComplex.LeftHomologyData.leftHomologyIso_hom_naturality φ S₁.leftHomologyData S₂.leftHomologyData

