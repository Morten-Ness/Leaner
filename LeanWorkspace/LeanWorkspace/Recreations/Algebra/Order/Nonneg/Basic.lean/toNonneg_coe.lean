import Mathlib

variable {α : Type*}

variable [Zero α] [SemilatticeSup α]

theorem toNonneg_coe {a : { x : α // 0 ≤ x }} : Nonneg.toNonneg (a : α) = a := Nonneg.toNonneg_of_nonneg a.2

