import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

theorem curryAlgEquiv_single (m : M) (n : N) (a : A) :
    MonoidAlgebra.curryAlgEquiv R (single (m, n) a) = single m (single n a) := by simp [MonoidAlgebra.curryAlgEquiv]

