import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem mapAlg_eq_map (S : Type v) [Semiring S] [Algebra R S] (p : R[X]) :
    Polynomial.mapAlg R S p = map (algebraMap R S) p := by
  rfl

