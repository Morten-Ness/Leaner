import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem commAlgEquiv_single_single (m : M) (n : N) (a : A) :
    MonoidAlgebra.commAlgEquiv R (single m <| single n a) = single n (single m a) := commRingEquiv_single_single ..

