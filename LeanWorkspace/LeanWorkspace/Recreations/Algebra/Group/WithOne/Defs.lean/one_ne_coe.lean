import Mathlib

variable {α : Type u}

theorem one_ne_coe {a : α} : (1 : WithOne α) ≠ a := WithOne.coe_ne_one.symm

