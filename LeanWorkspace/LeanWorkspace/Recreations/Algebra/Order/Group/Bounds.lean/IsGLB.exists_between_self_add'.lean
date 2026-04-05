import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε := h.exists_between' h₂ <| lt_add_of_pos_right _ hε

