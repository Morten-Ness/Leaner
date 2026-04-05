import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable (R) [CommSemiring R]

theorem grade_eq_lsingle_range (m : M) :
    grade R m = LinearMap.range (Finsupp.lsingle m : R →ₗ[R] M →₀ R) := Submodule.ext (AddMonoidAlgebra.mem_grade_iff' R m)

