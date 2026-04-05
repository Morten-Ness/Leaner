import Mathlib

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  [∀ (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ),
    CochainComplex.HasMapBifunctor K₁ K₂ F]

theorem commShiftIso_map₂CochainComplex_flip_inv_app (K₁ : CochainComplex C₁ ℤ)
    (K₂ : CochainComplex C₂ ℤ) (n : ℤ) :
    ((F.map₂CochainComplex.flip.obj K₂).commShiftIso n).inv.app K₁ =
      (CochainComplex.mapBifunctorShift₁Iso K₁ K₂ F n).inv := rfl

