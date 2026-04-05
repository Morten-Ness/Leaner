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

variable [DecidableEq ι₁₂] [HasMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄]

variable (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j j' : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j)

theorem ι_D₃ :
    HomologicalComplex.mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ HomologicalComplex.mapBifunctor₁₂.D₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' =
      HomologicalComplex.mapBifunctor₁₂.d₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j' := by
  simp only [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl h, HomologicalComplex.mapBifunctor₁₂.D₃, assoc, HomologicalComplex.mapBifunctor₁₂.ι_D₂ mapBifunctor]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq _ _ _ _ _ _ _ _ _ h₁]
    by_cases h₂ : ComplexShape.π c₁₂ c₃ c₄ (c₁.π c₂ c₁₂ (i₁, i₂), c₃.next i₃) = j'
    · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq mapBifunctor _ _ _ _ _ h₁ _ h₂,
        HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ h₂,
        Linear.comp_units_smul, smul_left_cancel_iff,
        HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl h₂,
        NatTrans.naturality_assoc]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂, comp_zero,
        HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₂, comp_zero, smul_zero]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero mapBifunctor _ _ _ _ _ _ _ h₁, comp_zero,
      HomologicalComplex.mapBifunctor₁₂.d₃_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₁]

