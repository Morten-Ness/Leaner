import Mathlib

variable {k G H : Type*}

variable [CommSemiring k] [Monoid G] [Monoid H]

variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

variable [MulSemiringAction G k] [SMulCommClass G k k]

theorem lift_def (F : G →* A) : (SkewMonoidAlgebra.lift k G A F : SkewMonoidAlgebra k G → A) =
    liftNC ((algebraMap k A : k →+* A) : k →+ A) F := rfl

