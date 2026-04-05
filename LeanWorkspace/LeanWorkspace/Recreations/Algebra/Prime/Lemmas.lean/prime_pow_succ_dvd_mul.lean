import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem prime_pow_succ_dvd_mul {p x y : M} (h : Prime p)
    {i : ℕ} (hxy : p ^ (i + 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y := by
  rw [or_iff_not_imp_right]
  exact fun a ↦ Prime.pow_dvd_of_dvd_mul_right h (i + 1) a hxy

