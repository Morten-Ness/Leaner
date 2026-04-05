import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem homologyFunctorFactorsh_inv_app_quotient_obj (K : CochainComplex C ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctorFactorsh C n).inv.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).hom.app _ ≫
      (DerivedCategory.homologyFunctorFactors C n).inv.app K ≫
        (DerivedCategory.homologyFunctor C n).map ((quotientCompQhIso C).inv.app K) := HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh_inv_app_quotient_obj ..

