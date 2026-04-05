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

variable (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j j' : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j)

theorem ι_D₁ :
    HomologicalComplex.mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j h ≫ HomologicalComplex.mapBifunctor₂₃.D₁ F G₂₃ K₁ K₂ K₃ c₂₃ c₄ j j' =
      HomologicalComplex.mapBifunctor₂₃.d₁ F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j' := by
  dsimp only [HomologicalComplex.mapBifunctor₂₃.D₁]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
      (by rw [← h, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; rfl),
    assoc, HomologicalComplex.mapBifunctor₁₂.ι_D₁ mapBifunctor]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [HomologicalComplex.mapBifunctor₂₃.d₁_eq _ _ _ _ _ _ _ _ h₁]
    by_cases h₂ : ComplexShape.π c₁ c₂₃ c₄ (c₁.next i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j'
    · rw [HomologicalComplex.mapBifunctor₂₃.d₁_eq mapBifunctor _ _ _ _ h₁ _ _ h₂, HomologicalComplex.mapBifunctor₂₃.ιOrZero_eq,
        Linear.comp_units_smul, NatTrans.naturality_assoc]
      · rfl
      · rw [← h₂, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]
        rfl
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂, comp_zero,
        HomologicalComplex.mapBifunctor₂₃.ιOrZero_eq_zero _ _ _ _ _ _ _ _ _ _ _ _
          (by simpa only [← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄] using h₂),
        comp_zero, smul_zero]
  · rw [HomologicalComplex.mapBifunctor₂₃.d₁_eq_zero mapBifunctor _ _ _ _ _ _ _ h₁,
      HomologicalComplex.mapBifunctor₂₃.d₁_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ h₁, comp_zero]

