import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem coe_mul_eq_bind {a : α} (ha : a ≠ 0) : ∀ b, (a * b : WithBot α) = b.bind fun b ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, ha, not_false_eq_true, mul_bot]; rfl
  | (b : α) => rfl
