import Mathlib

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

set_option backward.isDefEq.respectTransparency false in
theorem rightUnitor'_inv (i : I) :
    (HomologicalComplex.rightUnitor' K).inv i = (ρ_ (K.X i)).inv ≫ ((K.X i) ◁ (singleObjXSelf c 0 (𝟙_ C)).inv) ≫
      ιTensorObj K (tensorUnit C c) i 0 i (add_zero i) := by
  dsimp [HomologicalComplex.rightUnitor']
  rw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc, Iso.cancel_iso_inv_left,
    GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [id_tensorHom, ← whiskerLeft_comp_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom, Iso.hom_inv_id_assoc]
  dsimp [HomologicalComplex.tensorUnitIso]
  rw [dif_pos rfl]
  rfl

