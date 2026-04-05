import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem left_vsub_pointReflection (x y : P) : x -ᵥ pointReflection x y = y -ᵥ x := neg_injective <| by simp

