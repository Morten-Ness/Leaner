import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem min_one [LinearOrder α] : (1 : Finset α).min = 1 := rfl

