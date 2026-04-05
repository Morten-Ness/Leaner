import Mathlib

variable (R : Type u) (A : Type v) (B : Type w)

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem comp_ofId (φ : A →ₐ[R] B) : φ.comp (Algebra.ofId R A) = Algebra.ofId R B := by ext

