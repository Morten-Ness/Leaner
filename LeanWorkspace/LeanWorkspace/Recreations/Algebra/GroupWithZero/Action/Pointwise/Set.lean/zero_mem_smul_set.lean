import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

theorem zero_mem_smul_set (h : (0 : β) ∈ t) : (0 : β) ∈ a • t := ⟨0, h, smul_zero _⟩

