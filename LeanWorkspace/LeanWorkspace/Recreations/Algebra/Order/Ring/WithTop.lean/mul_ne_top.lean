import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem mul_ne_top {a b : WithTop α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b ≠ ⊤ := by
  simp [WithTop.mul_eq_top_iff, *]

