import Mathlib

variable {R S : Type*}

variable {m k : ℕ} (x y n : ℕ)

theorem sub_one_dvd_pow_sub_one : x - 1 ∣ x ^ n - 1 := by
  simpa using sub_dvd_pow_sub_pow x 1 n

