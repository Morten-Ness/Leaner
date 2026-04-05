import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem equivOfEq_trans (S T U : Subalgebra R A) (hST : S = T) (hTU : T = U) :
    (Subalgebra.equivOfEq S T hST).trans (Subalgebra.equivOfEq T U hTU) = Subalgebra.equivOfEq S U (hST.trans hTU) := rfl

