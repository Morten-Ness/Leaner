import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

theorem one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := Finset.one_mem_inv_mul_iff.not_left

