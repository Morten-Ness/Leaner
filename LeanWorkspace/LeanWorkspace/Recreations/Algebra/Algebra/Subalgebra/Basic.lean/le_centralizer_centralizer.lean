import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem le_centralizer_centralizer {s : Subalgebra R A} :
    s ≤ Subalgebra.centralizer R (Subalgebra.centralizer R (s : Set A)) := Set.subset_centralizer_centralizer

