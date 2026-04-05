import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem eval_map_algebraMap (P : R[X]) (b : B) :
    (map (algebraMap R B) P).eval b = Polynomial.aeval b P := by
  rw [Polynomial.aeval_def, Polynomial.eval_map]

