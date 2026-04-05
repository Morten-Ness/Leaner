import Mathlib

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]

set_option backward.isDefEq.respectTransparency false in
theorem homologyFunctorFactorsh_hom_app_quotient_obj
    (K : HomologicalComplex C c) (i : ι) :
    (HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C c i).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomologicalComplexUpToQuasiIso.homologyFunctor C c i).map ((HomologicalComplexUpToQuasiIso.quotientCompQhIso C c).hom.app K) ≫
      (HomologicalComplexUpToQuasiIso.homologyFunctorFactors C c i).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C c i).inv.app K := (Quotient.natTransLift_app ..).trans (by simp)

