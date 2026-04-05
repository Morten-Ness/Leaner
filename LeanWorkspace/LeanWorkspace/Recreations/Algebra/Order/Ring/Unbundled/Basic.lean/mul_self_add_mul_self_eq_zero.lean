import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_self_add_mul_self_eq_zero [NoZeroDivisors R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    a * a + b * b = 0 ↔ a = 0 ∧ b = 0 := by
  rw [add_eq_zero_iff_of_nonneg, mul_self_eq_zero (M₀ := R), mul_self_eq_zero (M₀ := R)] <;>
    apply mul_self_nonneg

