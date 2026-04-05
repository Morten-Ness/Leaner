import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem image_op_one [DecidableEq α] : (1 : Finset α).image op = 1 := rfl

