import Mathlib

variable {R : Type u} [CommSemiring R]

theorem braiding_naturality {X₁ X₂ Y₁ Y₂ : SemimoduleCat.{u} R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g) ≫ (Y₁.braiding Y₂).hom = (X₁.braiding X₂).hom ≫ (g ⊗ₘ f) := by
  ext : 1
  apply TensorProduct.ext'
  intro x y
  rfl

