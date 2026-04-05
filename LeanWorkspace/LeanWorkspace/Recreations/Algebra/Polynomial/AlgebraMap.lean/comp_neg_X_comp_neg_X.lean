import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem comp_neg_X_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) :
    (p.comp (-Polynomial.X)).comp (-Polynomial.X) = p := by
  rw [comp_assoc]
  simp only [neg_comp, X_comp, neg_neg, comp_X]

