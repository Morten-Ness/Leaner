import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_algHom (f : A →ₐ[R] B) (x : A) : Polynomial.aeval (f x) = f.comp (Polynomial.aeval x) := Polynomial.algHom_ext <| by simp only [Polynomial.aeval_X, AlgHom.comp_apply]

