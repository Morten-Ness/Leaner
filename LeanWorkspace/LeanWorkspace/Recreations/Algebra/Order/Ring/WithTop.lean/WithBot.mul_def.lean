import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem mul_def (a b : WithBot α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithBot.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

