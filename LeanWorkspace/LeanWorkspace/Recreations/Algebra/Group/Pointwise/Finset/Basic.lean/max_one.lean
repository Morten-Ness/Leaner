import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem max_one [LinearOrder α] : (1 : Finset α).max = 1 := rfl

