import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

variable {A : Type*} (B C : Type*) [CommSemiring A] [CommSemiring B] [Semiring C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

theorem mapAlg_comp (p : A[X]) : (Polynomial.mapAlg A Polynomial.C) p = (Polynomial.mapAlg B Polynomial.C) (Polynomial.mapAlg A B p) := by
  simp [Polynomial.mapAlg_eq_map, map_map, IsScalarTower.algebraMap_eq A B Polynomial.C]

