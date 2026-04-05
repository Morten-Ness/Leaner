import Mathlib

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

