import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem inf'_one [SemilatticeInf β] (f : α → β) : inf' 1 Finset.one_nonempty f = f 1 := rfl

