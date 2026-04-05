import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem mul_ne_bot {a b : WithBot α} (ha : a ≠ ⊥) (hb : b ≠ ⊥) : a * b ≠ ⊥ := WithTop.mul_ne_top (α := αᵒᵈ) ha hb

