import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_unique' (F : AlgHom k (SkewMonoidAlgebra k G) A) :
    F = SkewMonoidAlgebra.lift k G A ((F : SkewMonoidAlgebra k G →* A).comp (of k G)) := ((SkewMonoidAlgebra.lift k G A).apply_symm_apply F).symm

