import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem single_mem_grade {R} [CommSemiring R] (i : M) (r : R) :
    single i r ∈ grade R i := AddMonoidAlgebra.single_mem_gradeBy _ _ _

