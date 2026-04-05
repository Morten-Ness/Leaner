import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

theorem ext_from (i j : ℤ) (hij : j + 1 = i) {A : C} {f g : (CochainComplex.mappingCone φ).X j ⟶ A}
    (h₁ : (CochainComplex.mappingCone.inl φ).v i j (by lia) ≫ f = (CochainComplex.mappingCone.inl φ).v i j (by lia) ≫ g)
    (h₂ : (CochainComplex.mappingCone.inr φ).f j ≫ f = (CochainComplex.mappingCone.inr φ).f j ≫ g) :
    f = g := homotopyCofiber.ext_from_X φ i j hij h₁ h₂

