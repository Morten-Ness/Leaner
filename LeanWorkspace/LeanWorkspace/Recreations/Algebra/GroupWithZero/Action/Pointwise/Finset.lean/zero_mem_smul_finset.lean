import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

theorem zero_mem_smul_finset (h : (0 : β) ∈ t) : (0 : β) ∈ a • t := mem_smul_finset.2 ⟨0, h, smul_zero _⟩

