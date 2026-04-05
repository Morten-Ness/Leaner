import Mathlib

variable {F α β γ : Type*}

variable [One α] {s : Set α} {a : α}

theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 := subset_singleton_iff_eq

