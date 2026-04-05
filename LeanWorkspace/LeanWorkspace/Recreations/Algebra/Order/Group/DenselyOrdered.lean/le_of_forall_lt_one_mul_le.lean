import Mathlib

variable {α : Type*}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable [DenselyOrdered α] {a b : α}

theorem le_of_forall_lt_one_mul_le (h : ∀ ε < 1, a * ε ≤ b) : a ≤ b := le_of_forall_one_lt_le_mul (α := αᵒᵈ) h

