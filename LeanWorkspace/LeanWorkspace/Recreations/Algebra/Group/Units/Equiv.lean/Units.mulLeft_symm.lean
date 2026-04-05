import Mathlib

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N]

theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft := Equiv.ext fun _ => rfl

