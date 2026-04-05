import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ L₂ : CochainComplex C₂ ℤ) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive] (y : ℤ)
  [HasMapBifunctor K₁ K₂ F]

theorem mapBifunctorShift₂Iso_hom_naturality₂ [HasMapBifunctor K₁ L₂ F] :
    mapBifunctorMap (𝟙 K₁) (f₂⟦y⟧') F (.up ℤ) ≫ (CochainComplex.mapBifunctorShift₂Iso K₁ L₂ F y).hom =
      (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y).hom ≫ mapBifunctorMap (𝟙 K₁) f₂ F (.up ℤ)⟦y⟧' := by
  ext n p q h
  simp [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl,
    ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ _ _ _ _ _ _ (q + y) (n + y) rfl rfl]

