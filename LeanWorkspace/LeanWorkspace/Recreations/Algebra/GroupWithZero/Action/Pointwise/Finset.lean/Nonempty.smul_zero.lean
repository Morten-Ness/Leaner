import Mathlib

open scoped Pointwise

variable {α β : Type*} [DecidableEq β]

variable [Zero β] [SMulZeroClass α β] {s : Finset α} {t : Finset β} {a : α}

theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Finset β) = 0 := Finset.smul_zero_subset s.antisymm <| by simpa [mem_smul] using hs

