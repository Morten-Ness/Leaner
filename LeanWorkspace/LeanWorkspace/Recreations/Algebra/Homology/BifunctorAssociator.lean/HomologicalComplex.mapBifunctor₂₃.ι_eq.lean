import Mathlib

variable {C₁ C₂ C₁₂ C₂₃ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₁₂] [Category* C₂₃]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [Preadditive C₁₂] [Preadditive C₂₃] [Preadditive C₄]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F₁₂.obj X₁).PreservesZeroMorphisms]
  [G.Additive] [∀ (X₁₂ : C₁₂), (G.obj X₁₂).PreservesZeroMorphisms]
  [G₂₃.PreservesZeroMorphisms] [∀ (X₂ : C₂), (G₂₃.obj X₂).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {ι₁ ι₂ ι₃ ι₁₂ ι₂₃ ι₄ : Type*} [DecidableEq ι₄]
  {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} {c₃ : ComplexShape ι₃}
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (K₃ : HomologicalComplex C₃ c₃)
  (c₁₂ : ComplexShape ι₁₂) (c₂₃ : ComplexShape ι₂₃) (c₄ : ComplexShape ι₄)
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c₄]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c₄]
  [HasMapBifunctor K₁ K₂ F₁₂ c₁₂] [HasMapBifunctor K₂ K₃ G₂₃ c₂₃]
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄]

variable [DecidableEq ι₂₃] [HasMapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄]

theorem ι_eq (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (i₂₃ : ι₂₃) (j : ι₄)
    (h₂₃ : ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩ = i₂₃)
    (h : ComplexShape.π c₁ c₂₃ c₄ (i₁, i₂₃) = j) :
    HomologicalComplex.mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j
      (by rw [← h, ← h₂₃, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; rfl) =
      (F.obj (K₁.X i₁)).map (ιMapBifunctor K₂ K₃ G₂₃ c₂₃ i₂ i₃ i₂₃ h₂₃) ≫
        ιMapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄ i₁ i₂₃ j h := by
  subst h₂₃
  rfl

