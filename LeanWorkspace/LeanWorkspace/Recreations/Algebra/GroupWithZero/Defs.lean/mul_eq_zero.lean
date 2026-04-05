import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [MulZeroClass M₀]

variable [NoZeroDivisors M₀] {a b : M₀}

theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 := ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o ↦ o.elim (fun h ↦ mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

