import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

variable {f} (h : i₀ ≠ i₁) {K : HomologicalComplex C c} (φ₀ : X₀ ⟶ K.X i₀) (φ₁ : X₁ ⟶ K.X i₁)
  (comm : φ₀ ≫ K.d i₀ i₁ = f ≫ φ₁)
  (hφ : ∀ (k : ι), c.Rel i₁ k → φ₁ ≫ K.d i₁ k = 0)

theorem mkHomFromDouble_f₁ :
    (HomologicalComplex.mkHomFromDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₁ =
      (HomologicalComplex.doubleXIso₁ f hi₀₁ h).hom ≫ φ₁ := by
  dsimp [HomologicalComplex.mkHomFromDouble]
  rw [dif_neg h.symm, if_pos rfl, id_comp, comp_id]

