import Mathlib

variable {R S : Type*}

theorem toRatAlgHom_toRingHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) :
    ↑f.toRatAlgHom = f := RingHom.ext fun _x => rfl

