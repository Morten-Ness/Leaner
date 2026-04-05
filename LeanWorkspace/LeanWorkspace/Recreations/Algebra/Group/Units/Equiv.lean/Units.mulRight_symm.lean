import Mathlib

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N]

theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight := Equiv.ext fun _ => rfl

