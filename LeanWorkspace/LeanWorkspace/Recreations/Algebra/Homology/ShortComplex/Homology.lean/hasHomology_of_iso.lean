import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem hasHomology_of_iso (e : S₁ ≅ S₂) [HasHomology S₁] : HasHomology S₂ := CategoryTheory.ShortComplex.HasHomology.mk' (HomologyData.ofIso e S₁.homologyData)

