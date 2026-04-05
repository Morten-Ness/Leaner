import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

theorem IsKProjective.Qh_map_bijective [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (L : HomotopyCategory C (ComplexShape.up ℤ))
    [K.IsKProjective] :
    Function.Bijective (DerivedCategory.Qh.map :
      ((HomotopyCategory.quotient _ _).obj K ⟶ L) → _) := (CochainComplex.IsKProjective.leftOrthogonal K).map_bijective_of_isTriangulated _ _

