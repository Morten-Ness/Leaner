import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

variable (i₁ : I₁) (i₂ : I₂) (j : J)

theorem d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) :
    HomologicalComplex.mapBifunctor.d₂ K₁ K₂ F c i₁ i₂ j = 0 := HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ h

