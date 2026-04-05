import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [CommGroup α] [MulLeftMono α]

variable (s t : NonemptyInterval α) (a b : α)

theorem div_mem_div (ha : a ∈ s) (hb : b ∈ t) : a / b ∈ s / t := ⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩

