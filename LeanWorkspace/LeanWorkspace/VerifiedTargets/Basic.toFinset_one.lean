import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α]

theorem toFinset_one : (1 : Set α).toFinset = 1 := rfl

-- should take simp priority over `Finite.toFinset_singleton`

