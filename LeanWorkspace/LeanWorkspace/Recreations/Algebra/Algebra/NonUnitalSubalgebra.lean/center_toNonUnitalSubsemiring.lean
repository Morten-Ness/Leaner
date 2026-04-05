import Mathlib

variable {R A : Type*}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem center_toNonUnitalSubsemiring :
    (NonUnitalSubalgebra.center R A).toNonUnitalSubsemiring = NonUnitalSubsemiring.center A := rfl

