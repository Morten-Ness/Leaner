import Mathlib

variable {R S : Type*}

variable {m k : ℕ} (x y n : ℕ)

theorem pow_sub_pow_dvd_pow_sub_pow (hmk : m ∣ k) : x ^ m - y ^ m ∣ x ^ k - y ^ k := by
  obtain ⟨n, rfl⟩ := hmk; simpa [pow_mul] using sub_dvd_pow_sub_pow (x ^ m) (y ^ m) n

