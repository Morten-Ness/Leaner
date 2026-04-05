import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl

