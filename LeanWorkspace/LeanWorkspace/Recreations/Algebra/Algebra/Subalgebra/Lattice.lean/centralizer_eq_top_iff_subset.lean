import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

theorem centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s ⊆ center R A := SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

