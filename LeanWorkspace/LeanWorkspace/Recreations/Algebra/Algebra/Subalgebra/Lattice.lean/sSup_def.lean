import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem sSup_def (S : Set (Subalgebra R A)) : sSup S = Algebra.adjoin R (⋃₀ (SetLike.coe '' S)) := rfl

