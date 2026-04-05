import Mathlib

variable {α : Type*}

variable [One α] {p : Prop} [Decidable p] {a b : α}

theorem ite_lt_one [LT α] (ha : a < 1) (hb : b < 1) : ite p a b < 1 := by split <;> assumption

