import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem bot_mul' : ∀ (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊥ => (if_neg bot_ne_zero).symm
