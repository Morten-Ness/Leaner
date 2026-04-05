import Mathlib

variable {α : Type u}

variable [Group α] [LinearOrder α]

variable [MulLeftMono α]

variable {a b : α}

theorem le_iff_forall_one_lt_lt_mul : a ≤ b ↔ ∀ ε, 1 < ε → a < b * ε := ⟨fun h _ => lt_mul_of_le_of_one_lt h, le_of_forall_one_lt_lt_mul⟩

