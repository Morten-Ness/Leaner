import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable {A : Type*} (B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

theorem coeff_zero_of_isScalarTower (p : A[X]) :
    (algebraMap B Polynomial.C) ((algebraMap A B) (p.coeff 0)) = (Polynomial.mapAlg A Polynomial.C p).coeff 0 := by
  rw [Polynomial.mapAlg_eq_map, coeff_map, IsScalarTower.algebraMap_eq A B Polynomial.C, RingHom.comp_apply]

