import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = Polynomial.aeval 0 p := by
  simp [coeff_zero_eq_eval_zero]

