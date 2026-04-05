import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem add_eq_mul_one_add_div [Semiring R] {a : Rˣ} {b : R} : ↑a + b = a * (1 + ↑a⁻¹ * b) := by
  rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]

