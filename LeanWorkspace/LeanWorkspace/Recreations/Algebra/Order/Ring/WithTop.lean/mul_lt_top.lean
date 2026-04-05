import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem mul_lt_top [LT α] {a b : WithTop α} (ha : a < ⊤) (hb : b < ⊤) : a * b < ⊤ := by
  rw [WithTop.lt_top_iff_ne_top] at *
  exact WithTop.mul_ne_top ha hb

