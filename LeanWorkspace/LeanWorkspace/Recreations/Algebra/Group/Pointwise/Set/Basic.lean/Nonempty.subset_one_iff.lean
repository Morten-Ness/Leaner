import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 := h.subset_singleton_iff

