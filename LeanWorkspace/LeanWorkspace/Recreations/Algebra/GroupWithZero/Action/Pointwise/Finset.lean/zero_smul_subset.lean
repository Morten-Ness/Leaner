import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

theorem zero_smul_subset (t : Finset β) : (0 : Finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]

