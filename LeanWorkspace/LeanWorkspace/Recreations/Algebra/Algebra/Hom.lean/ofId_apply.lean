import Mathlib

variable (R : Type u) (A : Type v) (B : Type w)

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem ofId_apply (r) : Algebra.ofId R A r = algebraMap R A r := rfl

