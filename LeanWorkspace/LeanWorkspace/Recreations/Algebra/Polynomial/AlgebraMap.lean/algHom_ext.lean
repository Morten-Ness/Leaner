import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]

variable [Algebra R A] [Algebra R B]

variable {p q : R[X]} (x : A)

theorem algHom_ext {f g : R[X] →ₐ[R] B} (hX : f Polynomial.X = g Polynomial.X) :
    f = g := Polynomial.algHom_ext' (Subsingleton.elim ..) hX

