import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem mul_def (a b : WithTop α) :
    a * b = if a = 0 ∨ b = 0 then 0 else WithTop.map₂ (· * ·) a b := by
  cases a <;> cases b <;> aesop

