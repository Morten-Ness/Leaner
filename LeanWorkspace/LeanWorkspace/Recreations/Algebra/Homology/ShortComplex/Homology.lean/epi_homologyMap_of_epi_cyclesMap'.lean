import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem epi_homologyMap_of_epi_cyclesMap'
    [S₁.HasHomology] [S₂.HasHomology] (h : Epi (cyclesMap φ)) :
    Epi (CategoryTheory.ShortComplex.homologyMap φ) := by
  have : Epi (S₁.homologyπ ≫ CategoryTheory.ShortComplex.homologyMap φ) := by
    rw [CategoryTheory.ShortComplex.homologyπ_naturality φ]
    apply epi_comp
  exact epi_of_epi S₁.homologyπ (CategoryTheory.ShortComplex.homologyMap φ)

