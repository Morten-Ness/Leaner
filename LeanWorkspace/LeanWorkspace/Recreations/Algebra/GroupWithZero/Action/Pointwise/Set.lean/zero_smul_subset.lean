import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]

