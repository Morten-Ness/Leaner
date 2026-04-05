import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem coeff_mapAlgHom_apply (f : A →ₐ[R] B) (p : A[X]) (n : ℕ) :
    coeff (Polynomial.mapAlgHom f p) n = f (coeff p n) := by
  simp

