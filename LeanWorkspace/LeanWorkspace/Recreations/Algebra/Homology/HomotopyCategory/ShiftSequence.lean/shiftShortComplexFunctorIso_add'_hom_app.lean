import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
theorem shiftShortComplexFunctorIso_add'_hom_app
    (n m mn : ℤ) (hmn : m + n = mn) (a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (K : CochainComplex C ℤ) :
    (CochainComplex.shiftShortComplexFunctorIso C mn a a'' (by rw [← ha'', ← ha', ← add_assoc, hmn])).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n mn hmn).hom.app K) ≫
        (CochainComplex.shiftShortComplexFunctorIso C n a a' ha').hom.app (K⟦m⟧) ≫
        (CochainComplex.shiftShortComplexFunctorIso C m a' a'' ha'').hom.app K := by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

