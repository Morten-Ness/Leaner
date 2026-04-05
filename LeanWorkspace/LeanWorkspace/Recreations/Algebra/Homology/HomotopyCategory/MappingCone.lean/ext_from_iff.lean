import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem ext_from_iff (i j : ℤ) (hij : j + 1 = i) {A : C} (f g : (CochainComplex.mappingCone φ).X j ⟶ A) :
    f = g ↔ (CochainComplex.mappingCone.inl φ).v i j (by lia) ≫ f = (CochainComplex.mappingCone.inl φ).v i j (by lia) ≫ g ∧
      (CochainComplex.mappingCone.inr φ).f j ≫ f = (CochainComplex.mappingCone.inr φ).f j ≫ g := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact CochainComplex.mappingCone.ext_from φ i j hij h₁ h₂

