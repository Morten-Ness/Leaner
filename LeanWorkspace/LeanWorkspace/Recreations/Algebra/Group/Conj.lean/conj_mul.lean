import Mathlib

variable {α : Type u} {β : Type v}

variable [Group α]

theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ := by
  simp [mul_assoc]

