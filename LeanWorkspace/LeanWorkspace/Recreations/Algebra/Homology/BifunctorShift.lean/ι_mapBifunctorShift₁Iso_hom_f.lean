import Mathlib

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

