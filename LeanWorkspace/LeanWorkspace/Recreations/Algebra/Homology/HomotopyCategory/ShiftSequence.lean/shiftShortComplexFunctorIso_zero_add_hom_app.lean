import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
theorem shiftShortComplexFunctorIso_zero_add_hom_app (a : ℤ) (K : CochainComplex C ℤ) :
    (CochainComplex.shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  ext <;> simp [one_smul, shiftFunctorZero_hom_app_f]

