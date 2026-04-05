import Mathlib

section

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

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive] (x y : ℤ)
  [HasMapBifunctor K₁ K₂ F]

theorem mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso :
    CochainComplex.mapBifunctorShift₁Iso K₁ (K₂⟦y⟧) F x ≪≫
      (CategoryTheory.shiftFunctor _ x).mapIso (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y) =
      (x * y).negOnePow • (CochainComplex.mapBifunctorShift₂Iso (K₁⟦x⟧) K₂ F y ≪≫
        (CategoryTheory.shiftFunctor _ y).mapIso (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x) ≪≫
          (shiftFunctorComm (CochainComplex D ℤ) x y).app _) := by
  ext1
  dsimp [CochainComplex.mapBifunctorShift₁Iso, CochainComplex.mapBifunctorShift₂Iso]
  rw [Functor.map_comp, Functor.map_comp, assoc, assoc, assoc,
    ← HomologicalComplex₂.totalShift₁Iso_hom_naturality_assoc,
    HomologicalComplex₂.totalShift₁Iso_hom_totalShift₂Iso_hom,
    ← HomologicalComplex₂.totalShift₂Iso_hom_naturality_assoc,
    Linear.comp_units_smul, Linear.comp_units_smul,
    smul_left_cancel_iff,
    ← HomologicalComplex₂.total.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp_assoc]
  congr 2
  ext a b
  dsimp [HomologicalComplex₂.shiftFunctor₁₂CommIso]
  simp only [id_comp]

end

section

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

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ L₁ : CochainComplex C₁ ℤ) (f₁ : K₁ ⟶ L₁) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)
  [HasMapBifunctor K₁ K₂ F]

theorem ι_mapBifunctorShift₁Iso_hom_f (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n)
    (m₁ m : ℤ) (hm₁ : m₁ = n₁ + x) (hm : m = n + x) :
    ιMapBifunctor _ K₂ F n₁ n₂ n h ≫ (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F x).hom.f n =
      (F.map (shiftFunctorObjXIso K₁ x n₁ m₁ hm₁).hom).app _ ≫
        ιMapBifunctor K₁ K₂ F m₁ n₂ m (by lia) ≫
          (shiftFunctorObjXIso (mapBifunctor K₁ K₂ F) x n m hm).inv := by
  dsimp [CochainComplex.mapBifunctorShift₁Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₁Iso_hom_f _ _ _ _ _ _ _ hm₁ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₁XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

end

section

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [HasZeroMorphisms C₁] [Preadditive C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ L₂ : CochainComplex C₂ ℤ) (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive] (y : ℤ)
  [HasMapBifunctor K₁ K₂ F]

theorem ι_mapBifunctorShift₂Iso_hom_f (n₁ n₂ n : ℤ) (h : n₁ + n₂ = n)
    (m₂ m : ℤ) (hm₂ : m₂ = n₂ + y) (hm : m = n + y) :
    ιMapBifunctor K₁ _ F n₁ n₂ n h ≫ (CochainComplex.mapBifunctorShift₂Iso K₁ K₂ F y).hom.f n =
      (n₁ * y).negOnePow • (F.obj _).map (shiftFunctorObjXIso K₂ y n₂ m₂ hm₂).hom ≫
        ιMapBifunctor K₁ K₂ F n₁ m₂ m (by lia) ≫
        (shiftFunctorObjXIso (mapBifunctor K₁ K₂ F) y n m hm).inv := by
  dsimp [CochainComplex.mapBifunctorShift₂Iso]
  simp only [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ _ _ _ _ _ _ hm₂ _ hm]
  simp [HomologicalComplex₂.ιTotal, HomologicalComplex₂.shiftFunctor₂XXIso,
    HomologicalComplex.XIsoOfEq, eqToHom_map]

end
