import Mathlib

variable {α : Type u}

theorem coe_inj {a b : α} : (a : WithOne α) = b ↔ a = b := Option.some_inj

