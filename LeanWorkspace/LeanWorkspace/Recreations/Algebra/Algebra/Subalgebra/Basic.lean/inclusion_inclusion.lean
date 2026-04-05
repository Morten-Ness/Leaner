import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem inclusion_inclusion (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    Subalgebra.inclusion htu (Subalgebra.inclusion hst x) = Subalgebra.inclusion (le_trans hst htu) x := Subtype.ext rfl

