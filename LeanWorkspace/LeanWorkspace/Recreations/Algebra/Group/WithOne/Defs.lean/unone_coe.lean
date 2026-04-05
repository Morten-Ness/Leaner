import Mathlib

variable {α : Type u}

theorem unone_coe {x : α} (hx : (x : WithOne α) ≠ 1) : WithOne.unone hx = x := rfl

