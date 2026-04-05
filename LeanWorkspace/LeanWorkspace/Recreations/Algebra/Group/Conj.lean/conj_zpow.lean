import Mathlib

variable {α : Type u} {β : Type v}

variable [Group α]

theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  cases i
  · simp
  · simp only [zpow_negSucc, conj_pow, mul_inv_rev, inv_inv]
    rw [mul_assoc]

