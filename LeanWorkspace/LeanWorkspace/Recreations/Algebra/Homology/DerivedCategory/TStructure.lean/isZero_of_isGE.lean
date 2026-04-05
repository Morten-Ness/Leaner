import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isZero_of_isGE (X : DerivedCategory C) (n i : ℤ) (hi : i < n) [hX : X.IsGE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [DerivedCategory.isGE_iff] at hX
  exact hX i hi

