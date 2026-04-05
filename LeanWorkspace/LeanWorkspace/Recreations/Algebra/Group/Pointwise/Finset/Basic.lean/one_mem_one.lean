import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem one_mem_one : (1 : α) ∈ (1 : Finset α) := mem_singleton_self _

