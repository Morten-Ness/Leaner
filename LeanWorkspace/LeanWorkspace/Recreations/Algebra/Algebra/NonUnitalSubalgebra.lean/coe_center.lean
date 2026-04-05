import Mathlib

variable {R A : Type*}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem coe_center : (NonUnitalSubalgebra.center R A : Set A) = Set.center A := rfl

