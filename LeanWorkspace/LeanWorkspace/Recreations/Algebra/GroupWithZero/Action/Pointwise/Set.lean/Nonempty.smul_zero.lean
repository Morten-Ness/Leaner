import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Zero β] [SMulZeroClass α β] {s : Set α} {t : Set β} {a : α}

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 := Set.smul_zero_subset s.antisymm <| by simpa [mem_smul] using hs

