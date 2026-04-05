import Mathlib

variable {α : Type*}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable [DenselyOrdered α] {a b : α}

theorem le_of_forall_one_lt_div_le (h : ∀ ε : α, 1 < ε → a / ε ≤ b) : a ≤ b := le_of_forall_lt_one_mul_le fun ε ε1 => by
    simpa only [div_eq_mul_inv, inv_inv] using h ε⁻¹ (Left.one_lt_inv_iff.2 ε1)

