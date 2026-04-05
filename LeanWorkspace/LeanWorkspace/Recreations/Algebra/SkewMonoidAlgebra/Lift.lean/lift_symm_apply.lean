import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_symm_apply (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G) :
    (SkewMonoidAlgebra.lift k G A).symm F x = F (single x 1) := rfl

