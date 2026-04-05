import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem mul_eq_bot_iff : a * b = ⊥ ↔ a ≠ 0 ∧ b = ⊥ ∨ a = ⊥ ∧ b ≠ 0 := by rw [WithBot.mul_def]; aesop

