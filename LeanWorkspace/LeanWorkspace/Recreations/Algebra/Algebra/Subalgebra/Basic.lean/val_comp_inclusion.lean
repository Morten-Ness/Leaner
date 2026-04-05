import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem val_comp_inclusion (hst : S ≤ T) :
    T.val.comp (Subalgebra.inclusion hst) = S.val := rfl

