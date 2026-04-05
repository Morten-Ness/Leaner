import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_def (F : Multiplicative M →* A) :
    ⇑(AddMonoidAlgebra.lift R A M F) = liftNC ((algebraMap R A : R →+* A) : R →+ A) F := rfl

