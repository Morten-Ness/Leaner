import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem lift_def (F : M →* A) : ⇑(MonoidAlgebra.lift R A M F) = liftNC (algebraMap R A) F := rfl

