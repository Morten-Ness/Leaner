import Mathlib

open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

variable [CommSemiring R] [StarRing R] {f g : G → R}

theorem conjneg_ne_one : conjneg f ≠ 1 ↔ f ≠ 1 := conjneg_eq_one.not

