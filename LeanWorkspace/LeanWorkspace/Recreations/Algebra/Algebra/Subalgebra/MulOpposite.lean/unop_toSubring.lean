import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem unop_toSubring (S : Subalgebra R Aᵐᵒᵖ) : S.unop.toSubring = S.toSubring.unop := rfl

