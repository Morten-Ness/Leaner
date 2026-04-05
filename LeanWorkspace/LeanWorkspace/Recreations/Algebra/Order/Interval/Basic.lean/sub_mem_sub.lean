import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [Preorder α] [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α]

variable (s t : NonemptyInterval α) {a b : α}

theorem sub_mem_sub (ha : a ∈ s) (hb : b ∈ t) : a - b ∈ s - t := ⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩

