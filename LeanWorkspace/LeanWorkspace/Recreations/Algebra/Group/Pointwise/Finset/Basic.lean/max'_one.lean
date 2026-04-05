import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem max'_one [LinearOrder α] : (1 : Finset α).max' Finset.one_nonempty = 1 := rfl

