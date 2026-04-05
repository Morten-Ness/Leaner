import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isZero_of_isLE (X : DerivedCategory C) (n i : ℤ) (hi : n < i) [hX : X.IsLE n] :
    IsZero ((homologyFunctor _ i).obj X) := by
  rw [DerivedCategory.isLE_iff] at hX
  exact hX i hi

