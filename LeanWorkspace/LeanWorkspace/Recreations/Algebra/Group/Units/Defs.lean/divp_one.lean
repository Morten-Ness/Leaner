import Mathlib

variable {α : Type u}

variable [Monoid α] {a : α}

theorem divp_one (a : α) : a /ₚ 1 = a := mul_one _

