import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

variable {C} {A : C}

theorem homologyι_descOpcycles_eq_zero_of_boundary [S.HasHomology]
    (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.homologyι ≫ S.descOpcycles k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  dsimp only [CategoryTheory.ShortComplex.homologyι]
  rw [assoc, S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary k x hx, comp_zero]

