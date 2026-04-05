import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

theorem smul_zero_subset (s : Finset α) : s • (0 : Finset β) ⊆ 0 := by simp [subset_iff, mem_smul]

