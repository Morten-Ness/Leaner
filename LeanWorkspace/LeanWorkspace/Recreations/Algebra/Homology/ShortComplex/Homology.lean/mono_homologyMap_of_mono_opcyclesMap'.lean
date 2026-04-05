import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem mono_homologyMap_of_mono_opcyclesMap'
    [S₁.HasHomology] [S₂.HasHomology] (h : Mono (opcyclesMap φ)) :
    Mono (CategoryTheory.ShortComplex.homologyMap φ) := by
  have : Mono (CategoryTheory.ShortComplex.homologyMap φ ≫ S₂.homologyι) := by
    rw [CategoryTheory.ShortComplex.homologyι_naturality φ]
    apply mono_comp
  exact mono_of_mono (CategoryTheory.ShortComplex.homologyMap φ) S₂.homologyι

