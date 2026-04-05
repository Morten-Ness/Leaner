import Mathlib

variable {α : Type u} {β : Type v}

variable [Group α]

theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ := by
  simp [mul_assoc]

