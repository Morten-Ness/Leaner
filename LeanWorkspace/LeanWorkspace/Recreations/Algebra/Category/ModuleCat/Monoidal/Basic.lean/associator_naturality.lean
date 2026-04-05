import Mathlib

variable {R : Type u} [CommSemiring R]

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    SemimoduleCat.MonoidalCategory.tensorHom (SemimoduleCat.MonoidalCategory.tensorHom f₁ f₂) f₃ ≫ (SemimoduleCat.MonoidalCategory.associator Y₁ Y₂ Y₃).hom =
      (SemimoduleCat.MonoidalCategory.associator X₁ X₂ X₃).hom ≫ SemimoduleCat.MonoidalCategory.tensorHom f₁ (SemimoduleCat.MonoidalCategory.tensorHom f₂ f₃) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

