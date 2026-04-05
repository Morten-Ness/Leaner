import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem re_mul : (a * b).re = a.re * b.re - a.imI * b.imI - a.imJ * b.imJ - a.imK * b.imK := (QuaternionAlgebra.re_mul a b).trans <| by simp [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

