import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

theorem single_algebraMap_eq_algebraMap_mul_of (m : M) (r : R) :
    single m (algebraMap R A r) = algebraMap R A[M] r * of A M m := by simp

