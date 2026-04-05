import Mathlib

open scoped DirectSum

variable {ι : Type uι}

variable (R : Type uR) (A : ι → Type uA) {B : Type uB}

variable [CommSemiring R] [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]

variable [AddMonoid ι] [GSemiring A]

variable [Semiring B] [GAlgebra R A] [Algebra R B]

variable [DecidableEq ι]

theorem algebraMap_apply (r : R) :
    algebraMap R (⨁ i, A i) r = DirectSum.of A 0 (GAlgebra.toFun r) := rfl

