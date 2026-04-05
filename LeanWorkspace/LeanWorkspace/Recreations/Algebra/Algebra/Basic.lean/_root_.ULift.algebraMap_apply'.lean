import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem _root_.ULift.algebraMap_apply' (r : ULift R) :
    algebraMap (ULift R) A r = algebraMap R A r.down := rfl

