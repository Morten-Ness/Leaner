import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (j j' : J) (i₁ : I₁) (i₂ : I₂) (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j)

theorem ι_D₁ :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ HomologicalComplex.mapBifunctor.D₁ K₁ K₂ F c j j' = HomologicalComplex.mapBifunctor.d₁ K₁ K₂ F c i₁ i₂ j' := by
  apply HomologicalComplex₂.ι_D₁

