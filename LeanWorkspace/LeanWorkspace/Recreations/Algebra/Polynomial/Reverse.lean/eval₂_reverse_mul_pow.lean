import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

variable {S : Type*} [CommSemiring S]

theorem eval₂_reverse_mul_pow (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟x) (Polynomial.reverse f) * x ^ f.natDegree = eval₂ i x f := Polynomial.eval₂_reflect_mul_pow i _ _ f le_rfl

