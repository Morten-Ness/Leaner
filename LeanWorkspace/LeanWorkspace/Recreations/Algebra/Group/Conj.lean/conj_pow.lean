import Mathlib

variable {α : Type u} {β : Type v}

variable [Group α]

theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction i with
  | zero => simp
  | succ i hi => simp [pow_succ, hi]

