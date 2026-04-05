import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem aeval_smul (f : R[X]) {G : Type*} [Monoid G] [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) (x : A) : f.aeval (g • x) = g • (f.aeval x) := by
  rw [← MulSemiringAction.toAlgHom_apply R, Polynomial.aeval_algHom_apply, MulSemiringAction.toAlgHom_apply]

