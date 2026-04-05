import Mathlib

variable {M : Type*}

theorem Associated.of_pow_associated_of_prime' [CommMonoidWithZero M] [IsCancelMulZero M]
    {p₁ p₂ : M} {k₁ k₂ : ℕ}
    (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₂ : 0 < k₂) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ := Associated.symm (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂)

