import Mathlib

variable {M : Type*}

variable {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R] [Subsingleton Rˣ]

variable {p₁ p₂ : R} {k₁ k₂ : ℕ}

theorem eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂) (hk₁ : 0 < k₁)
    (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂ := by
  rw [← associated_iff_eq] at h ⊢
  apply h.of_pow_associated_of_prime hp₁ hp₂ hk₁

