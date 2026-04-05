import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem inf_one [SemilatticeInf β] [OrderTop β] (f : α → β) : inf 1 f = f 1 := inf_singleton

