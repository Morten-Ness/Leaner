import Mathlib

open scoped DirectSum

variable {ι : Type uι}

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

variable [Semiring B] [GAlgebra R A] [Algebra R B]

variable [DecidableEq ι]

theorem algebraMap_toAddMonoid_hom :
    ↑(algebraMap R (⨁ i, A i)) = (DirectSum.of A 0).comp (GAlgebra.toFun : R →+ A 0) := rfl

