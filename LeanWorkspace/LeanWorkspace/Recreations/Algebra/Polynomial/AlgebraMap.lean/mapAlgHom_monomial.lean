import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgHom_monomial (f : A →ₐ[R] B) (n : ℕ) (a : A) :
    Polynomial.mapAlgHom f (monomial n a) = monomial n (f a) := by simp

