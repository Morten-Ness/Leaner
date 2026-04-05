import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem ext_to_iff (i j : ℤ) (hij : i + 1 = j) {A : C} (f g : A ⟶ (CochainComplex.mappingCone φ).X i) :
    f = g ↔ f ≫ (CochainComplex.mappingCone.fst φ).1.v i j hij = g ≫ (CochainComplex.mappingCone.fst φ).1.v i j hij ∧
      f ≫ (CochainComplex.mappingCone.snd φ).v i i (add_zero i) = g ≫ (CochainComplex.mappingCone.snd φ).v i i (add_zero i) := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨h₁, h₂⟩
    exact CochainComplex.mappingCone.ext_to φ i j hij h₁ h₂

