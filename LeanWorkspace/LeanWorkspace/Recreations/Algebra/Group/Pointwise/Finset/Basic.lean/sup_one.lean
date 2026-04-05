import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem sup_one [SemilatticeSup β] [OrderBot β] (f : α → β) : sup 1 f = f 1 := sup_singleton

