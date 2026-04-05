import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem center_toSubring (R A : Type*) [CommRing R] [Ring A] [Algebra R A] :
    (Subalgebra.center R A).toSubring = Subring.center A := rfl

