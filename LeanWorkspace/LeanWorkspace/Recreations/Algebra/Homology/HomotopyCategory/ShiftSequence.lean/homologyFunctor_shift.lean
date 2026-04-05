import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable [CategoryWithHomology C]

theorem homologyFunctor_shift (n : ℤ) :
    (homologyFunctor C (ComplexShape.up ℤ) 0).shift n =
      homologyFunctor C (ComplexShape.up ℤ) n := rfl

