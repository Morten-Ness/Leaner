import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B]

variable (g : R →ₐ[S] A') (y : A')

theorem aevalTower_id : Polynomial.aevalTower (AlgHom.id S S) = Polynomial.aeval := by
  ext s
  simp only [eval_X, Polynomial.aevalTower_X, Polynomial.coe_aeval_eq_eval]

