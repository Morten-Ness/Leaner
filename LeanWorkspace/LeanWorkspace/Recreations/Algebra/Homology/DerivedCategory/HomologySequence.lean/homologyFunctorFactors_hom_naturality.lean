import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

set_option backward.isDefEq.respectTransparency false in
theorem homologyFunctorFactors_hom_naturality
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    (DerivedCategory.homologyFunctor C n).map (Q.map f) ≫ (DerivedCategory.homologyFunctorFactors C n).hom.app L =
    (DerivedCategory.homologyFunctorFactors C n).hom.app K ≫ HomologicalComplex.homologyMap f n := (DerivedCategory.homologyFunctorFactors C n).hom.naturality f

