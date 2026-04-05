import Mathlib

variable {R S : Type*}

theorem AlgHom.toRingHom_toRatAlgHom [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f := AlgHom.ext fun _x => rfl

