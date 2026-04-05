import Mathlib

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_pow (r : M₀) : ∀ n : ℕ, r⁻¹ʳ ^ n = (r ^ n)⁻¹ʳ
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succ', pow_succ, Ring.mul_inverse_rev' ((Commute.refl r).pow_left n),
      Ring.inverse_pow r n]
