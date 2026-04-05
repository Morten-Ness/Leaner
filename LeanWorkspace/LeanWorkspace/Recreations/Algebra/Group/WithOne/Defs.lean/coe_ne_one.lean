import Mathlib

variable {α : Type u}

theorem coe_ne_one {a : α} : (a : WithOne α) ≠ (1 : WithOne α) := Option.some_ne_none a

