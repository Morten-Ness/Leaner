import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem singleton_one : ({1} : Finset α) = 1 := rfl

