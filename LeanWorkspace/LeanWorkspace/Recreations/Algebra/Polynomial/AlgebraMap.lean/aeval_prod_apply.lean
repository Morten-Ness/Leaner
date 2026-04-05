import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_prod_apply (x : A × B) (p : Polynomial R) :
    p.aeval x = (p.aeval x.1, p.aeval x.2) := by simp [Polynomial.aeval_prod]

