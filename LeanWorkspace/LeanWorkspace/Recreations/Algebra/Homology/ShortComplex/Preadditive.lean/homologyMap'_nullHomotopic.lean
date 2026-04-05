import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {S₁ S₂ S₃ : ShortComplex C}

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

theorem homologyMap'_nullHomotopic
    (H₁ : S₁.HomologyData) (H₂ : S₂.HomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap' (CategoryTheory.ShortComplex.nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 := by
  apply CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic

