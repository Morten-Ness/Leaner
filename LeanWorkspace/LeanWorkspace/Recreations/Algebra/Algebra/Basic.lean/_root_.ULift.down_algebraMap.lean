import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem _root_.ULift.down_algebraMap (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r := rfl

