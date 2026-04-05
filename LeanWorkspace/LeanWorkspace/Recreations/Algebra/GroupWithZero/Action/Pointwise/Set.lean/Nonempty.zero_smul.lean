import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 := Set.zero_smul_subset t.antisymm <| by simpa [mem_smul] using ht

