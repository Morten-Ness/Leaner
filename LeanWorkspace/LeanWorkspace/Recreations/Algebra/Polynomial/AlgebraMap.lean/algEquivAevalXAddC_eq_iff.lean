import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem algEquivAevalXAddC_eq_iff {R : Type*} [CommRing R] (t t' : R) :
    Polynomial.algEquivAevalXAddC t = Polynomial.algEquivAevalXAddC t' ↔ t = t' := by
  simp [Polynomial.algEquivAevalXAddC]

