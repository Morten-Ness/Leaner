import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ := rfl

