import Mathlib

variable (ι : Type*)

variable {R : Type*}

variable (A : ι → Type*)

variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

variable (S : ι → Type*) [∀ i, CommSemiring (S i)]

variable (A B : Type*) [Semiring B] [Algebra R B]

theorem constAlgHom_eq_algebra_ofId : Pi.constAlgHom R A R = Algebra.ofId R (A → R) := rfl

