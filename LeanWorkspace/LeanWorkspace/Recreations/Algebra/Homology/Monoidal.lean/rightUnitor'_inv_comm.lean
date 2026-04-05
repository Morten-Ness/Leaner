import Mathlib

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

set_option backward.isDefEq.respectTransparency false in
theorem rightUnitor'_inv_comm (i j : I) :
    (HomologicalComplex.rightUnitor' K).inv i ≫ (tensorObj K (tensorUnit C c)).d i j =
      K.d i j ≫ (HomologicalComplex.rightUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [HomologicalComplex.rightUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      HomologicalComplex.tensor_unit_d₂, comp_zero, add_zero]
    rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
    dsimp
    simp only [one_smul, whisker_exchange_assoc, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

