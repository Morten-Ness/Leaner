import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem equivOfEq_symm (S T : Subalgebra R A) (h : S = T) :
    (Subalgebra.equivOfEq S T h).symm = Subalgebra.equivOfEq T S h.symm := rfl

