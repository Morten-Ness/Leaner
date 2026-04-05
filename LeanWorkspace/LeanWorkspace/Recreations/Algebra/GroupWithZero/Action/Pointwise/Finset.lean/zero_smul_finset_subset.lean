import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

theorem zero_smul_finset_subset (s : Finset β) : (0 : α) • s ⊆ 0 := image_subset_iff.2 fun x _ ↦ mem_zero.2 <| zero_smul α x

