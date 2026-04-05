import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable (S) {A : C}

variable [HasHomology S]

theorem homologyι_comp_fromOpcycles :
    S.homologyι ≫ S.fromOpcycles = 0 := by
  dsimp only [CategoryTheory.ShortComplex.homologyι]
  simp only [assoc, rightHomologyι_comp_fromOpcycles, comp_zero]

