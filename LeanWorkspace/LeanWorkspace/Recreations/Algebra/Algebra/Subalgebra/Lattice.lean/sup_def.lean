import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem sup_def (S T : Subalgebra R A) : S ⊔ T = Algebra.adjoin R (S ∪ T : Set A) := rfl

