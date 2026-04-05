import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem one_notMem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t := Finset.one_mem_div_iff.not_left

