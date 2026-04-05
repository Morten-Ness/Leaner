import Mathlib

variable {R S : Type*}

variable {m k : ℕ} (x y n : ℕ)

theorem pow_sub_one_dvd_pow_sub_one (hmk : m ∣ k) : x ^ m - 1 ∣ x ^ k - 1 := by
  simpa using Nat.pow_sub_pow_dvd_pow_sub_pow x 1 hmk

