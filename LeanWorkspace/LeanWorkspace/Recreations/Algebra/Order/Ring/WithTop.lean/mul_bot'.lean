import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem mul_bot' : ∀ (a : WithBot α), a * ⊥ = if a = 0 then 0 else ⊥
  | (a : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm
