import Mathlib

section

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

theorem mapBifunctorAssociatorX_hom_D₁ (j j' : ι₄) :
    (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j).hom ≫
      mapBifunctor₂₃.D₁ F G₂₃ K₁ K₂ K₃ c₂₃ c₄ j j' =
        mapBifunctor₁₂.D₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' ≫
        (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j').hom := by
  ext i₁ i₂ i₃ h
  rw [mapBifunctor₁₂.ι_D₁_assoc, ι_mapBifunctorAssociatorX_hom_assoc, HomologicalComplex.mapBifunctor₁₂.ι_D₁ mapBifunctor₂₃]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · have := NatTrans.naturality_app_app associator.hom
      (K₁.d i₁ (c₁.next i₁)) (K₂.X i₂) (K₃.X i₃)
    dsimp at this
    rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq mapBifunctor₁₂ _ _ _ _ _ _ _ h₁, HomologicalComplex.mapBifunctor₁₂.d₁_eq mapBifunctor₂₃ _ _ _ _ _ _ _ _ h₁,
      Linear.comp_units_smul, Linear.units_smul_comp, assoc,
        ComplexShape.associative_ε₁_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c₄,
      HomologicalComplex.ιOrZero_mapBifunctorAssociatorX_hom, smul_left_cancel_iff,
      reassoc_of% this]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero mapBifunctor₁₂ _ _ _ _ _ _ _ _ _ _ _ h₁,
      HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ _ _ _ h₁, comp_zero, zero_comp]

end

section

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

theorem mapBifunctorAssociatorX_hom_D₂ (j j' : ι₄) :
    (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j).hom ≫
      mapBifunctor₂₃.D₂ F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ j j' =
        mapBifunctor₁₂.D₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' ≫
        (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j').hom := by
  ext i₁ i₂ i₃ h
  rw [mapBifunctor₁₂.ι_D₂_assoc, ι_mapBifunctorAssociatorX_hom_assoc, HomologicalComplex.mapBifunctor₁₂.ι_D₂ mapBifunctor₂₃]
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · have := NatTrans.naturality_app (associator.hom.app (K₁.X i₁)) (K₃.X i₃) (K₂.d i₂ (c₂.next i₂))
    dsimp at this
    rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq mapBifunctor₁₂ _ _ _ _ _ _ _ _ h₁, HomologicalComplex.mapBifunctor₁₂.d₂_eq mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ h₁,
      Linear.units_smul_comp, assoc, HomologicalComplex.ιOrZero_mapBifunctorAssociatorX_hom,
      reassoc_of% this, Linear.comp_units_smul,
      ComplexShape.associative_ε₂_ε₁ c₁ c₂ c₃ c₁₂ c₂₃ c₄]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero mapBifunctor₁₂ _ _ _ _ _ _ _ _ _ _ _ h₁,
      HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ _ _ _ h₁, comp_zero, zero_comp]

end

section

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

end

section

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

theorem ιOrZero_mapBifunctorAssociatorX_hom (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄) :
    mapBifunctor₁₂.ιOrZero F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j ≫
    (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j).hom =
      ((associator.hom.app (K₁.X i₁)).app (K₂.X i₂)).app (K₃.X i₃) ≫
        mapBifunctor₂₃.ιOrZero F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j := by
  by_cases h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j
  · rw [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq mapBifunctor₁₂ _ _ _ _ _ _ _ _ _ _ _ h,
      HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ _ _ _ h,
      HomologicalComplex.ι_mapBifunctorAssociatorX_hom]
  · rw [HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq_zero mapBifunctor₁₂ _ _ _ _ _ _ _ _ _ _ _ h,
      HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq_zero mapBifunctor₂₃ _ _ _ _ _ _ _ _ _ _ _ _ h,
      zero_comp, comp_zero]

end

section

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

theorem ι_mapBifunctorAssociatorX_hom (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫
    (HomologicalComplex.mapBifunctorAssociatorX associator K₁ K₂ K₃ c₁₂ c₂₃ c₄ j).hom =
      ((associator.hom.app (K₁.X i₁)).app (K₂.X i₂)).app (K₃.X i₃) ≫
        mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j h := by
  apply GradedObject.ι_mapBifunctorAssociator_hom

end

section

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

variable [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] {j : ι₄} {A : C₄}
  (f : ∀ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (_ : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j),
        (G.obj ((F₁₂.obj (K₁.X i₁)).obj (K₂.X i₂))).obj (K₃.X i₃) ⟶ A)

theorem ι_mapBifunctor₁₂Desc (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    HomologicalComplex.mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫ HomologicalComplex.mapBifunctor₁₂.mapBifunctor₁₂Desc f =
      f i₁ i₂ i₃ h := by
  apply GradedObject.ι_mapBifunctor₁₂BifunctorDesc

end

section

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

variable [HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]

variable {j : ι₄} {A : C₄}
  (f : ∀ (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (_ : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j),
        (F.obj (K₁.X i₁)).obj ((G₂₃.obj (K₂.X i₂)).obj (K₃.X i₃)) ⟶ A)

theorem ι_mapBifunctor₂₃Desc (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    HomologicalComplex.mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j h ≫ HomologicalComplex.mapBifunctor₂₃.mapBifunctor₂₃Desc c₁₂ f =
      f i₁ i₂ i₃ h := by
  apply GradedObject.ι_mapBifunctorBifunctor₂₃Desc

end
