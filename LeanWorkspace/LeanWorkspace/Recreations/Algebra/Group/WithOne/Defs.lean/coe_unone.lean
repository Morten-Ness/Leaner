import Mathlib

variable {α : Type u}

theorem coe_unone : ∀ {x : WithOne α} (hx : x ≠ 1), WithOne.unone hx = x
  | (x : α), _ => rfl
