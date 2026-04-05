import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r := toFinsupp_injective (Polynomial.toFinsupp_algebraMap _).symm

