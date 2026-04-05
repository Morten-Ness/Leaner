import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

theorem congr_left_φH {γ₁ γ₂ : CategoryTheory.ShortComplex.HomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) :
    γ₁.left.φH = γ₂.left.φH := by rw [eq]

