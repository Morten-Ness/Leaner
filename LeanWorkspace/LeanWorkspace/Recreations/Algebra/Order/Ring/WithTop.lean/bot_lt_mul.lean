import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem bot_lt_mul [LT α] {a b : WithBot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b := WithTop.mul_lt_top (α := αᵒᵈ) ha hb

