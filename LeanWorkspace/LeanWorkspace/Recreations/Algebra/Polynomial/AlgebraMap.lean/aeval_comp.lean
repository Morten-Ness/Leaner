import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_comp {A : Type*} [Semiring A] [Algebra R A] (x : A) :
    Polynomial.aeval x (p.comp q) = Polynomial.aeval (Polynomial.aeval x q) p := eval₂_comp' x p q

