import Mathlib

open scoped AlgebraMonoidAlgebra

variable {R S T A B C M N O : Type*}

variable [CommMonoid M] [CommSemiring R] [CommSemiring S] [Algebra R S]

theorem algebraMap_def : algebraMap R[M] S[M] = mapRingHom M (algebraMap R S) := rfl

