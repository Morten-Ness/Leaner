import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B]

variable (g : R →ₐ[S] A') (y : A')

theorem aevalTower_toAlgHom (x : R) : Polynomial.aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x := Polynomial.aevalTower_algebraMap _ _ _

