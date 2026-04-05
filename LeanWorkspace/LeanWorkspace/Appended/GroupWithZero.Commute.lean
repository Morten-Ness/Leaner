import Mathlib

section

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem inverse_pow_mul_eq_iff_eq_mul {a : M₀} (b c : M₀) (ha : IsUnit a) {k : ℕ} :
    a⁻¹ʳ ^ k * b = c ↔ b = a ^ k * c := by
  rw [Ring.inverse_pow, Ring.inverse_mul_eq_iff_eq_mul _ _ _ (IsUnit.pow _ ha)]

end

section

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ := Ring.mul_inverse_rev' (Commute.all _ _)

end
