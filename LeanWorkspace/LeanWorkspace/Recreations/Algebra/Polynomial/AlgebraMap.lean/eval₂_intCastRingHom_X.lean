import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable {p q r : R[X]}

theorem eval₂_intCastRingHom_X {R : Type*} [Ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f Polynomial.X) p = f p := Polynomial.eval₂_algebraMap_X p f.toIntAlgHom

