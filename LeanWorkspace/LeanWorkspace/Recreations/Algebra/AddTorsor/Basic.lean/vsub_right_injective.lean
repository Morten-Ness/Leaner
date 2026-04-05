import Mathlib

open scoped Pointwise

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_right_injective (p : P) : Function.Injective ((p -ᵥ ·) : P → G) := fun _ _ =>
  vsub_right_cancel

