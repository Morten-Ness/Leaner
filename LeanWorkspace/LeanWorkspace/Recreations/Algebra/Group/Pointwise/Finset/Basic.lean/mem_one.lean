import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 := mem_singleton

