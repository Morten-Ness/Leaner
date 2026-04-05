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

theorem d_eq (j j' : ι₄) [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄] :
    (mapBifunctor (mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄).d j j' =
      HomologicalComplex.mapBifunctor₁₂.D₁ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' + HomologicalComplex.mapBifunctor₁₂.D₂ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' +
        HomologicalComplex.mapBifunctor₁₂.D₃ F₁₂ G K₁ K₂ K₃ c₁₂ c₄ j j' := by
  rw [mapBifunctor.d_eq]
  congr 1
  ext i₁ i₂ i₃ h
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₁₂.ι_D₁, HomologicalComplex.mapBifunctor₁₂.ι_D₂]
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ rfl h, assoc, HomologicalComplex.mapBifunctor₁₂.ι_D₁ mapBifunctor]
  set i₁₂ := ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  by_cases h₁ : c₁₂.Rel i₁₂ (c₁₂.next i₁₂)
  · by_cases h₂ : ComplexShape.π c₁₂ c₃ c₄ (c₁₂.next i₁₂, i₃) = j'
    · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq mapBifunctor _ _ _ _ h₁ _ _ h₂]
      simp only [i₁₂, mapBifunctor.d_eq, Functor.map_add, NatTrans.app_add,
        Preadditive.add_comp, smul_add, Preadditive.comp_add, Linear.comp_units_smul]
      congr 1
      · rw [← NatTrans.comp_app_assoc, ← Functor.map_comp,
          HomologicalComplex.mapBifunctor₁₂.ι_D₁ mapBifunctor]
        by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
        · have h₄ := (ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂).symm
          rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq mapBifunctor _ _ _ _ h₃ _ _ h₄,
            HomologicalComplex.mapBifunctor₁₂.d₁_eq _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ (by rw [← h₂, ← h₄]; rfl),
            HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ (c₁₂.next i₁₂) _ h₄ h₂,
            Functor.map_units_smul, Functor.map_comp, NatTrans.app_units_zsmul,
            NatTrans.comp_app, Linear.units_smul_comp, assoc, smul_smul]
        · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero mapBifunctor _ _ _ _ _ _ _ h₃,
            Functor.map_zero, zero_app, zero_comp, smul_zero]
      · rw [← NatTrans.comp_app_assoc, ← Functor.map_comp,
          HomologicalComplex.mapBifunctor₁₂.ι_D₂ mapBifunctor]
        by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
        · have h₄ := (ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃).symm
          rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq mapBifunctor _ _ _ _ _ h₃ _ h₄,
            HomologicalComplex.mapBifunctor₁₂.d₂_eq _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ (by rw [← h₂, ← h₄]; rfl),
            HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ _ _ _ (c₁₂.next i₁₂) _ h₄ h₂,
            Functor.map_units_smul, Functor.map_comp, NatTrans.app_units_zsmul,
            NatTrans.comp_app, Linear.units_smul_comp, assoc, smul_smul]
        · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero mapBifunctor _ _ _ _ _ _ _ h₃,
            Functor.map_zero, zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂, comp_zero]
      trans 0 + 0
      · simp
      · congr 1
        · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
          · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq _ _ _ _ _ _ _ h₃, HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq_zero, comp_zero, smul_zero]
            dsimp [ComplexShape.r]
            intro h₄
            apply h₂
            rw [← h₄, ComplexShape.next_π₁ c₂ c₁₂ h₃ i₂]
          · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃]
        · by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
          · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq _ _ _ _ _ _ _ _ h₃, HomologicalComplex.mapBifunctor₁₂.ιOrZero_eq_zero, comp_zero, smul_zero]
            dsimp [ComplexShape.r]
            intro h₄
            apply h₂
            rw [← h₄, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃]
          · rw [HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero _ _ _ _ _ _ _ _ _ _ _ h₃]
  · rw [HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero mapBifunctor _ _ _ _ _ _ _ h₁, comp_zero,
      HomologicalComplex.mapBifunctor₁₂.d₁_eq_zero, HomologicalComplex.mapBifunctor₁₂.d₂_eq_zero, zero_add]
    · intro h₂
      apply h₁
      have := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂
      rw [c₁₂.next_eq' this]
      exact this
    · intro h₂
      apply h₁
      have := ComplexShape.rel_π₁ c₂ c₁₂ h₂ i₂
      rw [c₁₂.next_eq' this]
      exact this

