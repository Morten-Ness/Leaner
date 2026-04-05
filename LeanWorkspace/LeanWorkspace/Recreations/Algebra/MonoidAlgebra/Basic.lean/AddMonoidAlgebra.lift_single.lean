import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_single (F : Multiplicative M →* A) (a b) :
    AddMonoidAlgebra.lift R A M F (single a b) = b • F (Multiplicative.ofAdd a) := MonoidAlgebra.lift_single F (.ofAdd a) b

