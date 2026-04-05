import Mathlib

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

set_option backward.isDefEq.respectTransparency false in
theorem leftUnitor'_inv (i : I) :
    (HomologicalComplex.leftUnitor' K).inv i = (λ_ (K.X i)).inv ≫ ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ (K.X i)) ≫
      ιTensorObj (tensorUnit C c) K 0 i i (zero_add i) := by
  dsimp [HomologicalComplex.leftUnitor']
  rw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc, Iso.cancel_iso_inv_left,
    GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [tensorHom_id, ← comp_whiskerRight_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom, Iso.hom_inv_id_assoc]
  dsimp [HomologicalComplex.tensorUnitIso]
  rw [dif_pos rfl]
  rfl

