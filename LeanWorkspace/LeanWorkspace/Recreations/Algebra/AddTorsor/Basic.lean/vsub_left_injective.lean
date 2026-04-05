import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_left_injective (p : P) : Function.Injective ((· -ᵥ p) : P → G) := fun _ _ =>
  vsub_left_cancel

