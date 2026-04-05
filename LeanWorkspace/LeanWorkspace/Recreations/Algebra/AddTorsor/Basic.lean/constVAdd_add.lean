import Mathlib

open scoped Pointwise

variable (G : Type*) (P : Type*) [AddGroup G] [AddTorsor G P]

theorem constVAdd_add (v₁ v₂ : G) : constVAdd P (v₁ + v₂) = constVAdd P v₁ * constVAdd P v₂ := ext <| add_vadd v₁ v₂

