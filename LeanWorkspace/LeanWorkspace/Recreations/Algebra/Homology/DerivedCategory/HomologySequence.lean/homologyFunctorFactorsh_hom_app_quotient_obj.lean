import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem homologyFunctorFactorsh_hom_app_quotient_obj (K : CochainComplex C ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctorFactorsh C n).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (DerivedCategory.homologyFunctor C n).map ((quotientCompQhIso C).hom.app K) ≫
      (DerivedCategory.homologyFunctorFactors C n).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).inv.app _ := HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_hom_app_quotient_obj ..

