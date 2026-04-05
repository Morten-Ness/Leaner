import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem algebraMap_pUnit (r : R) : algebraMap R PUnit r = PUnit.unit := rfl

