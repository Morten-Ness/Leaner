import Mathlib

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

set_option backward.isDefEq.respectTransparency false in
theorem leftUnitor'_inv_comm (i j : I) :
    (HomologicalComplex.leftUnitor' K).inv i ≫ (tensorObj (tensorUnit C c) K).d i j =
      K.d i j ≫ (HomologicalComplex.leftUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [HomologicalComplex.leftUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      HomologicalComplex.unit_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    dsimp
    simp only [ComplexShape.ε_zero, one_smul, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

