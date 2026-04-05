import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem dvd_pow_sub_one_of_dvd {r : R} {a b : ℕ} (h : a ∣ b) :
    r ^ a - 1 ∣ r ^ b - 1 := by
  obtain ⟨n, rfl⟩ := h
  exact pow_one_sub_dvd_pow_mul_sub_one r a n

