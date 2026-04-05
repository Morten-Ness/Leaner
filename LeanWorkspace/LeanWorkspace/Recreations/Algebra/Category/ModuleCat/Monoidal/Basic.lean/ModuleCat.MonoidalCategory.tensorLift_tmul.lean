import Mathlib

variable {R : Type u} [CommRing R]

variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}

variable (f : M₁ → M₂ → M₃) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

theorem tensorLift_tmul (m : M₁) (n : M₂) :
    ModuleCat.MonoidalCategory.tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl

