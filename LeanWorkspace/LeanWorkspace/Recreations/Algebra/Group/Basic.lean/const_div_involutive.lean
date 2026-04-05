import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem const_div_involutive (a : G) : Function.Involutive (a / ·) := fun _ ↦ div_div_cancel ..

