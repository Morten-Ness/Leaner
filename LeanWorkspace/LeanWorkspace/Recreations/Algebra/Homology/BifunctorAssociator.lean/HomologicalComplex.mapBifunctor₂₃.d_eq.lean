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

variable [HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄] (j j' : ι₄)

theorem d_eq :
    (mapBifunctor K₁ (mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄).d j j' =
      HomologicalComplex.mapBifunctor₂₃.D₁ F G₂₃ K₁ K₂ K₃ c₂₃ c₄ j j' + HomologicalComplex.mapBifunctor₂₃.D₂ F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ j j' +
      HomologicalComplex.mapBifunctor₂₃.D₃ F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ j j' := by
  rw [HomologicalComplex.mapBifunctor₁₂.d_eq mapBifunctor]
  rw [add_assoc]
  congr 1
  apply HomologicalComplex.mapBifunctor₂₃.hom_ext HomologicalComplex.mapBifunctor₂₃ (c₁₂ := c₁₂)
  intro i₁ i₂ i₃ h
  simp only [Preadditive.comp_add, HomologicalComplex.mapBifunctor₂₃.ι_D₂, HomologicalComplex.mapBifunctor₂₃.ι_D₃]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
      (by rw [← h, ← ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]; rfl),
    assoc, HomologicalComplex.mapBifunctor₂₃.ι_D₂ mapBifunctor]
  set i₂₃ := ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩
  by_cases h₁ : c₂₃.Rel i₂₃ (c₂₃.next i₂₃)
  · by_cases h₂ : ComplexShape.π c₁ c₂₃ c₄ (i₁, c₂₃.next i₂₃) = j'
    · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq mapBifunctor _ _ _ _ _ h₁ _ h₂, HomologicalComplex.mapBifunctor₁₂.d_eq mapBifunctor,
        Linear.comp_units_smul, Functor.map_add, Preadditive.add_comp,
        Preadditive.comp_add, smul_add]
      congr 1
      · rw [← Functor.map_comp_assoc, HomologicalComplex.mapBifunctor₂₃.ι_D₁ mapBifunctor]
        by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
        · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq _ _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₂₃.d₁_eq mapBifunctor _ _ _ _ h₃ _ _ (ComplexShape.next_π₁ c₃ c₂₃ h₃ i₃).symm,
            Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp,
            assoc, smul_smul, smul_left_cancel_iff,
            HomologicalComplex.mapBifunctor₂₃.ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ _ (by
              dsimp [ComplexShape.r]
              rw [← h₂, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄,
                ComplexShape.next_π₁ c₃ c₂₃ h₃ i₃]), HomologicalComplex.mapBifunctor₂₃.ι_eq]
        · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₂₃.d₁_eq_zero mapBifunctor _ _ _ _ _ _ _ h₃,
            Functor.map_zero, zero_comp, smul_zero]
      · rw [← Functor.map_comp_assoc, HomologicalComplex.mapBifunctor₂₃.ι_D₂ mapBifunctor]
        by_cases h₃ : c₃.Rel i₃ (c₃.next i₃)
        · rw [HomologicalComplex.mapBifunctor₂₃.d₃_eq _ _ _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₂₃.d₂_eq mapBifunctor _ _ _ _ _ h₃ _ (ComplexShape.next_π₂ c₂ c₂₃ i₂ h₃).symm,
            Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp, assoc,
            smul_smul, smul_left_cancel_iff]
          rw [HomologicalComplex.mapBifunctor₂₃.ιOrZero_eq _ _ _ _ _ _ _ _ _ _ _ _ (by
            dsimp [ComplexShape.r]
            rw [← h₂, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄, ComplexShape.next_π₂ c₂ c₂₃ i₂ h₃]),
            HomologicalComplex.mapBifunctor₂₃.ι_eq]
        · rw [HomologicalComplex.mapBifunctor₂₃.d₃_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ h₃,
            HomologicalComplex.mapBifunctor₂₃.d₂_eq_zero mapBifunctor _ _ _ _ _ _ _ h₃,
            Functor.map_zero, zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂, comp_zero]
      trans 0 + 0
      · simp
      · congr 1
        · by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
          · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq _ _ _ _ _ _ _ _ _ h₃, HomologicalComplex.mapBifunctor₂₃.ιOrZero_eq_zero, comp_zero, smul_zero]
            intro h₄
            apply h₂
            rw [← h₄]
            dsimp [ComplexShape.r]
            rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄, ComplexShape.next_π₁ c₃ c₂₃ h₃ i₃]
          · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ h₃]
        · by_cases h₃ : c₃.Rel i₃ (c₃.next i₃)
          · rw [HomologicalComplex.mapBifunctor₂₃.d₃_eq _ _ _ _ _ _ _ _ _ _ h₃, HomologicalComplex.mapBifunctor₂₃.ιOrZero_eq_zero, comp_zero, smul_zero]
            intro h₄
            apply h₂
            rw [← h₄]
            dsimp [ComplexShape.r]
            rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄, ComplexShape.next_π₂ c₂ c₂₃ i₂ h₃]
          · rw [HomologicalComplex.mapBifunctor₂₃.d₃_eq_zero _ _ _ _ _ _ _ _ _ _ _ _ h₃]
  · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq_zero mapBifunctor _ _ _ _ _ _ _ h₁, comp_zero]
    trans 0 + 0
    · simp only [add_zero]
    · congr 1
      · rw [HomologicalComplex.mapBifunctor₂₃.d₂_eq_zero]
        intro h₂
        apply h₁
        simpa only [← ComplexShape.next_π₁ c₃ c₂₃ h₂ i₃]
          using ComplexShape.rel_π₁ c₃ c₂₃ h₂ i₃
      · rw [HomologicalComplex.mapBifunctor₂₃.d₃_eq_zero]
        intro h₂
        apply h₁
        simpa only [i₂₃, ComplexShape.next_π₂ c₂ c₂₃ i₂ h₂]
          using ComplexShape.rel_π₂ c₂ c₂₃ i₂ h₂

