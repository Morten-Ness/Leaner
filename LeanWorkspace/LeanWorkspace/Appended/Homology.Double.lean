import Mathlib

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem from_double_hom_ext {K : HomologicalComplex C c} {φ φ' : HomologicalComplex.double f hi₀₁ ⟶ K}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (HomologicalComplex.isZero_double_X f hi₀₁ k h.1 h.2).eq_of_src

end

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem isZero_double_X (k : ι) (h₀ : k ≠ i₀) (h₁ : k ≠ i₁) :
    IsZero ((HomologicalComplex.double f hi₀₁).X k) := by
  dsimp [HomologicalComplex.double]
  rw [if_neg h₀, if_neg h₁]
  exact Limits.isZero_zero C

end

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

variable {f} (h : i₀ ≠ i₁) {K : HomologicalComplex C c} (φ₀ : X₀ ⟶ K.X i₀) (φ₁ : X₁ ⟶ K.X i₁)
  (comm : φ₀ ≫ K.d i₀ i₁ = f ≫ φ₁)
  (hφ : ∀ (k : ι), c.Rel i₁ k → φ₁ ≫ K.d i₁ k = 0)

theorem mkHomFromDouble_f₀ :
    (HomologicalComplex.mkHomFromDouble hi₀₁ h φ₀ φ₁ comm hφ).f i₀ =
      (HomologicalComplex.doubleXIso₀ f hi₀₁).hom ≫ φ₀ := by
  dsimp [HomologicalComplex.mkHomFromDouble]
  rw [if_pos rfl, id_comp, comp_id]

end

section

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

end

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem to_double_hom_ext {K : HomologicalComplex C c} {φ φ' : K ⟶ HomologicalComplex.double f hi₀₁}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (HomologicalComplex.isZero_double_X f hi₀₁ k h.1 h.2).eq_of_tgt

end
