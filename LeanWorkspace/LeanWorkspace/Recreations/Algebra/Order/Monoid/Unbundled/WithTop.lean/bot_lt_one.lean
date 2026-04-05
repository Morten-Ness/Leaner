import Mathlib

variable {α : Type u} {β : Type v}

variable [One α] {a : α}

theorem bot_lt_one [LT α] : ⊥ < (1 : WithBot α) := bot_lt_coe _

