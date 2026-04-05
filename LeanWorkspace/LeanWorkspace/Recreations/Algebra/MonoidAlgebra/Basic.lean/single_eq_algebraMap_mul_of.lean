import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

theorem single_eq_algebraMap_mul_of (m : M) (r : R) :
    single m r = algebraMap R R[M] r * of R M m := by simp

