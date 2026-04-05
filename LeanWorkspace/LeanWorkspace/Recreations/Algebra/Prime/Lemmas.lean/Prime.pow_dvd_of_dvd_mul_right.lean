import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem Prime.pow_dvd_of_dvd_mul_right {p a b : M} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a := by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'

