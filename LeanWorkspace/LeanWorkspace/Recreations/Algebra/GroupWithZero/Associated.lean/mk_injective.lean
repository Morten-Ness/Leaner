import Mathlib

variable {M : Type*}

theorem mk_injective [Monoid M] [Subsingleton Mˣ] : Function.Injective (@Associates.mk M _) := fun _ _ h => associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

