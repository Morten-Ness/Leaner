import Mathlib

open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

variable [CommSemiring R] [StarRing R] {f g : G → R}

theorem conjneg_ne_conjneg : conjneg f ≠ conjneg g ↔ f ≠ g := conjneg_injective.ne_iff

