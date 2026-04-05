import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem asIsoHomologyπ_inv_comp_homologyπ (hf : S.f = 0) [S.HasHomology] :
    (S.asIsoHomologyπ hf).inv ≫ S.homologyπ = 𝟙 _ := Iso.inv_hom_id _

