import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a := h.exists_between <| sub_lt_self _ hε

