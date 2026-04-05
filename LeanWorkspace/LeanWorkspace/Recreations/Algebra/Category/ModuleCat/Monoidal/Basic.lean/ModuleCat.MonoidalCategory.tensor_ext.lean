import Mathlib

variable {R : Type u} [CommRing R]

variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}

theorem tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃} (h : ∀ m n, f.hom (m ⊗ₜ n) = g.hom (m ⊗ₜ n)) :
    f = g := hom_ext <| TensorProduct.ext (by ext; apply h)

