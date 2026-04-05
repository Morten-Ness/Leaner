import Mathlib

variable {α : Type*}

variable [One α] {p : Prop} [Decidable p] {a b : α}

theorem one_le_ite [LE α] (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ ite p a b := by split <;> assumption

