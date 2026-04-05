import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem toCycles_comp_homologyπ :
    S.toCycles ≫ S.homologyπ = 0 := by
  dsimp only [CategoryTheory.ShortComplex.homologyπ]
  simp only [toCycles_comp_leftHomologyπ_assoc, zero_comp]

