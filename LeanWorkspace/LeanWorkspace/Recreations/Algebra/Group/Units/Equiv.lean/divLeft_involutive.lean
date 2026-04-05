import Mathlib

variable {F α M N G : Type*}

variable [CommGroup G]

theorem divLeft_involutive (a : G) : Function.Involutive (Equiv.divLeft a) := fun _ ↦ div_div_cancel ..

