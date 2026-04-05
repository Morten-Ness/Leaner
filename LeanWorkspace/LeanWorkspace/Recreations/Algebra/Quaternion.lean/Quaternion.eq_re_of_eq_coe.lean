import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re := QuaternionAlgebra.eq_re_of_eq_coe h

