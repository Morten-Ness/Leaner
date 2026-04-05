import Mathlib

variable {α : Type u}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable {a b : α}

theorem le_of_forall_one_lt_lt_mul (h : ∀ ε : α, 1 < ε → a < b * ε) : a ≤ b := le_of_not_gt fun h₁ => lt_irrefl a (by simpa using h _ (lt_inv_mul_iff_lt.mpr h₁))

