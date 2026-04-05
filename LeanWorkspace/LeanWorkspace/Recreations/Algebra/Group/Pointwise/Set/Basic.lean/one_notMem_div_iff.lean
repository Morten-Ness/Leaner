import Mathlib

variable {F α β γ : Type*}

variable [Group α] {s t : Set α} {a b : α}

theorem one_notMem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t := Set.one_mem_div_iff.not_left

