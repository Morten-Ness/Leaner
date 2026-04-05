import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imK_mul : (a * b).imK = a.re * b.imK + a.imI * b.imJ - a.imJ * b.imI + a.imK * b.re := (QuaternionAlgebra.imK_mul a b).trans <| by ring

