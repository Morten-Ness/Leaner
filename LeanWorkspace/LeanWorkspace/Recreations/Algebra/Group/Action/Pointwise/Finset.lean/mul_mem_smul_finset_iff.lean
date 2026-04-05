import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem mul_mem_smul_finset_iff [DecidableEq α] (a : α) {b : α} {s : Finset α} :
    a * b ∈ a • s ↔ b ∈ s := Finset.smul_mem_smul_finset_iff _

