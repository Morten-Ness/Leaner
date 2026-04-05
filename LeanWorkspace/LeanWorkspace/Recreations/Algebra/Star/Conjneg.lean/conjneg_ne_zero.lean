import Mathlib

open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

variable [CommSemiring R] [StarRing R] {f g : G → R}

theorem conjneg_ne_zero : conjneg f ≠ 0 ↔ f ≠ 0 := conjneg_eq_zero.not

