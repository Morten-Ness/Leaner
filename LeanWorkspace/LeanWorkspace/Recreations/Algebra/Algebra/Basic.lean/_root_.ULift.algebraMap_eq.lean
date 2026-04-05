import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem _root_.ULift.algebraMap_eq (r : R) :
    algebraMap R (ULift A) r = ULift.up (algebraMap R A r) := rfl

