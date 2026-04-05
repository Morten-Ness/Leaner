import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem center_le_centralizer (s) : Subalgebra.center R A ≤ Subalgebra.centralizer R s := s.center_subset_centralizer

