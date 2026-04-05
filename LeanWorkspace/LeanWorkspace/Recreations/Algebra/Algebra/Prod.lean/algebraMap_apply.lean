import Mathlib

variable {R A B C : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B] [Semiring C] [Algebra R C]

theorem algebraMap_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) := rfl

