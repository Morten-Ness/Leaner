import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : CochainComplex C₁ ℤ) (f₁ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F]

theorem mapBifunctorShift₁Iso_hom_naturality₁ [HasMapBifunctor L₁ K₂ F] :
    mapBifunctorMap (f₁⟦x⟧') (𝟙 K₂) F (.up ℤ) ≫ (CochainComplex.mapBifunctorShift₁Iso L₁ K₂ F x).hom =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x).hom ≫ mapBifunctorMap f₁ (𝟙 K₂) F (.up ℤ)⟦x⟧' := by
  ext n p q h
  simp [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl,
    ι_mapBifunctorShift₁Iso_hom_f_assoc _ _ _ _ _ _ _ _ (p + x) (n + x) rfl rfl]

