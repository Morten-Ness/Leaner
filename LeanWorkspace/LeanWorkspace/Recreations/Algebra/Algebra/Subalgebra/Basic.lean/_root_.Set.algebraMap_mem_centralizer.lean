import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S T U : Subalgebra R A)

variable {S T U} (h : S ≤ T)

theorem _root_.Set.algebraMap_mem_centralizer {s : Set A} (r : R) :
    algebraMap R A r ∈ s.centralizer := fun _a _h => (Algebra.commutes _ _).symm

