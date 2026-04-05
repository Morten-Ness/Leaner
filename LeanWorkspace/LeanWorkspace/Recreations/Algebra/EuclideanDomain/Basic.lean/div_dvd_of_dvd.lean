import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm, ← EuclideanDomain.mul_div_assoc _ hpq, mul_comm, mul_div_cancel_right₀ _ hq]

