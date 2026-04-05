import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

variable {S : Type*} [CommSemiring S]

theorem eval₂_reverse_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟x) (Polynomial.reverse f) = 0 ↔ eval₂ i x f = 0 := Polynomial.eval₂_reflect_eq_zero_iff i x _ _ le_rfl

