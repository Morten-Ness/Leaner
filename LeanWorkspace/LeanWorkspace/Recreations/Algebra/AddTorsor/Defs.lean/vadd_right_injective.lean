import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vadd_right_injective (p : P) : Function.Injective ((· +ᵥ p) : G → P) := fun _ _ =>
  vadd_right_cancel p

