import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 := image_subset_iff.2 fun x _ ↦ zero_smul α x

