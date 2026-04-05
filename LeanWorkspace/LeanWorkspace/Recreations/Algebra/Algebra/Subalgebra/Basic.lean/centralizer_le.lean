import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : Subalgebra.centralizer R t ≤ Subalgebra.centralizer R s := Set.centralizer_subset h

