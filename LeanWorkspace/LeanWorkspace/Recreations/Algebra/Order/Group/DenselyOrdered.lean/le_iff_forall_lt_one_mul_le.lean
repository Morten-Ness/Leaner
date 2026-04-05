import Mathlib

variable {α : Type*}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable [DenselyOrdered α] {a b : α}

theorem le_iff_forall_lt_one_mul_le : a ≤ b ↔ ∀ ε < 1, a * ε ≤ b := le_iff_forall_one_lt_le_mul (α := αᵒᵈ)

