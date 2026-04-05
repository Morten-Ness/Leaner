import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [PartialOrder α] [One α]

theorem one_mem_one : (1 : α) ∈ (1 : NonemptyInterval α) := ⟨le_rfl, le_rfl⟩

