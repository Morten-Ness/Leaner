import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem top_mul' : ∀ (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤
  | (b : α) => if_congr coe_eq_zero.symm rfl rfl
  | ⊤ => (if_neg top_ne_zero).symm
