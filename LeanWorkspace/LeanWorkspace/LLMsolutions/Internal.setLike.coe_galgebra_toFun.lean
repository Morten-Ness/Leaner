FAIL
import Mathlib

variable {ι : Type*} {σ S R : Type*}

variable [DecidableEq ι]

theorem setLike.coe_galgebra_toFun {ι} [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    ((DirectSum.GAlgebra.toFun (A := A) s : A 0) : R) = algebraMap S R s := rfl
