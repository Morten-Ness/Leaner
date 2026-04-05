import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms D]
  (F : C₁ ⥤ C₂ ⥤ D) {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)
  [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]

theorem mapBifunctorHomologicalComplex_obj_obj_toGradedObject
    (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂) :
    (((CategoryTheory.Functor.mapBifunctorHomologicalComplex F c₁ c₂).obj K₁).obj K₂).toGradedObject =
      ((GradedObject.mapBifunctor F I₁ I₂).obj K₁.X).obj K₂.X := rfl

