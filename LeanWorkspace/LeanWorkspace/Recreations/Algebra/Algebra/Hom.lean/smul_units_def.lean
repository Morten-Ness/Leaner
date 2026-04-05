import Mathlib

variable (R : Type u) (A : Type v) (B : Type w)

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem smul_units_def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := rfl

