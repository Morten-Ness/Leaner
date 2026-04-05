import Mathlib

variable {α : Type*}

variable [One α] {p : Prop} [Decidable p] {a b : α}

theorem one_lt_ite [LT α] (ha : 1 < a) (hb : 1 < b) : 1 < ite p a b := by split <;> assumption

