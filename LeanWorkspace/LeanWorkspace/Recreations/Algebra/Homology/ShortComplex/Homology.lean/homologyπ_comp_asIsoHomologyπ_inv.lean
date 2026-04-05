import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem homologyπ_comp_asIsoHomologyπ_inv (hf : S.f = 0) [S.HasHomology] :
    S.homologyπ ≫ (S.asIsoHomologyπ hf).inv = 𝟙 _ := (S.asIsoHomologyπ hf).hom_inv_id

