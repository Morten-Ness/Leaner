import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mul_mem_nonZeroDivisors : a * b ∈ M₀⁰ ↔ a ∈ M₀⁰ ∧ b ∈ M₀⁰ where
  mp h := by
    rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]
    constructor <;> intro x h' <;> apply h.2
    · rw [← mul_assoc, h', zero_mul]
    · rw [mul_comm a b, ← mul_assoc, h', zero_mul]
  mpr := fun h ↦ mul_mem h.1 h.2

