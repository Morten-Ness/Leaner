import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : HomologicalComplex C₁ c₁) (K₂ L₂ : HomologicalComplex C₂ c₂)
  (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [TotalComplexShape c₁ c₂ c]

variable [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c] [DecidableEq J]

set_option backward.isDefEq.respectTransparency false in
theorem ι_mapBifunctorMap (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (HomologicalComplex.mapBifunctorMap f₁ f₂ F c).f j =
      (F.map (f₁.f i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctor L₁ L₂ F c i₁ i₂ j h := by
  simp [HomologicalComplex.mapBifunctorMap]

