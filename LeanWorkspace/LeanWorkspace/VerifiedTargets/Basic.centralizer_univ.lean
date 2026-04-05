import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem centralizer_univ : Subalgebra.centralizer R Set.univ = Subalgebra.center R A := SetLike.ext' (Set.centralizer_univ A)

