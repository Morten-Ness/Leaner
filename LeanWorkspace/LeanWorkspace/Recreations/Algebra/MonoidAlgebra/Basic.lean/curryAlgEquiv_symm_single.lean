import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

theorem curryAlgEquiv_symm_single (m : M) (n : N) (a : A) :
    (MonoidAlgebra.curryAlgEquiv R).symm (single m <| single n a) = (single (m, n) a) := by
  classical exact Finsupp.uncurry_single ..

