import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]

