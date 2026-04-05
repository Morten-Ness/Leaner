import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem mapAlgEquiv_comp (Polynomial.C : Type*) [Semiring Polynomial.C] [Algebra R Polynomial.C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] Polynomial.C) :
    (Polynomial.mapAlgEquiv f).trans (Polynomial.mapAlgEquiv g) = Polynomial.mapAlgEquiv (f.trans g) := by
  ext
  simp

