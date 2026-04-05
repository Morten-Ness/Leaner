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

variable [DecidableEq ι₁₂] [DecidableEq ι₂₃]
  [HasMapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄]
  [HasMapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄]
  [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
  [HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]

theorem mapBifunctorAssociatorX_hom_D₃ (j j' : ι₄) :
    (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j).hom ≫
      mapBifunctor₂₃.D₃ F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ j j' =
        mapBifunctor₁₂.D₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' ≫
        (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j').hom := by
  ext i₁ i₂ i₃ h
  rw [mapBifunctor₁₂.ι_D₃_assoc, ι_mapBifunctorAssociatorX_hom_assoc, HomologicalComplex.mapBifunctor₁₂.ι_D₃ mapBifunctor₂₃]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq mapBifunctor₁₂ _ _ _ _ _ _ _ _ _ h₁,
      HomologicalComplex.mapBifunctor₁₂.d₃_eq mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ _ h₁,
      Linear.comp_units_smul, Linear.units_smul_comp, assoc,
      HomologicalComplex.ιOrZero_mapBifunctorAssociatorX_hom, NatTrans.naturality_assoc,
      ComplexShape.associative_ε₂_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c₄]
    dsimp
  · rw [HomologicalComplex.mapBifunctor₁₂.d₃_eq_zero mapBifunctor₁₂ _ _ _ _ _ _ _ _ _ _ _ h₁,
      HomologicalComplex.mapBifunctor₁₂.d₃_eq_zero mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ _ _ _ h₁, comp_zero, zero_comp]

