import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_X_left_eq_map [CommSemiring S] [Algebra R S] (p : R[X]) :
    Polynomial.aeval Polynomial.X p = map (algebraMap R S) p := rfl

