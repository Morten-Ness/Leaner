import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_one : Polynomial.aeval x (1 : R[X]) = 1 := map_one _

