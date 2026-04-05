import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem IsKInjective.Qh_map_bijective [HasDerivedCategory C]
    (K : HomotopyCategory C (ComplexShape.up ℤ))
    (L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      (K ⟶ (HomotopyCategory.quotient _ _).obj L) → _) := (CochainComplex.IsKInjective.rightOrthogonal L).map_bijective_of_isTriangulated _ _

