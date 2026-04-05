import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem constVAdd_zero : constVAdd P (0 : G) = 1 := ext <| zero_vadd G

