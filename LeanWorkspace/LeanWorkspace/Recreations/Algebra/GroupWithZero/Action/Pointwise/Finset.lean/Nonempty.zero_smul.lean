import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Finset α} {t : Finset β}

theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Finset α) • t = 0 := Finset.zero_smul_subset t.antisymm <| by simpa [mem_smul] using ht

