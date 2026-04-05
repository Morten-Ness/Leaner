import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [AddMonoid M] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem lift_of' (F : Multiplicative M →* A) (x : M) :
    AddMonoidAlgebra.lift R A M F (of' R M x) = F (Multiplicative.ofAdd x) := AddMonoidAlgebra.lift_of F x

