import Mathlib

open scoped ComplexConjugate

variable {ι G R : Type*} [AddGroup G]

variable [CommSemiring R] [StarRing R] {f g : G → R}

theorem conjneg_injective : Function.Injective (conjneg : (G → R) → G → R) := conjneg_involutive.injective

