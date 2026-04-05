import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) :
    Polynomial.aeval (algebraMap R A x) p = algebraMap R A (p.eval x) := Polynomial.aeval_algHom_apply (Algebra.ofId R A) x p

