import Mathlib

variable {α β G M : Type*}

variable [DivisionMonoid α] {a b c d : α}

theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 := mt eq_of_div_eq_one

