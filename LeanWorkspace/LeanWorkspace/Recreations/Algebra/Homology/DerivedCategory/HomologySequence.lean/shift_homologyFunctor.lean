import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem shift_homologyFunctor (n : ℤ) :
    (DerivedCategory.homologyFunctor C 0).shift n = DerivedCategory.homologyFunctor C n := rfl

