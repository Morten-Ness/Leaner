import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_op_apply (x : A) (p : R[X]) :
    Polynomial.aeval (MulOpposite.op x) p = MulOpposite.op (Polynomial.aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n c => simp [Polynomial.aeval_monomial, MulOpposite.op_pow, Algebra.commutes]

