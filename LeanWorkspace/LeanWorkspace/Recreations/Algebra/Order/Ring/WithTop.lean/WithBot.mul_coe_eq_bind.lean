import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem mul_coe_eq_bind {b : α} (hb : b ≠ 0) : ∀ a, (a * b : WithBot α) = a.bind fun a ↦ ↑(a * b)
  | ⊥ => by simp only [ne_eq, coe_eq_zero, hb, not_false_eq_true, bot_mul]; rfl
  | (a : α) => rfl
