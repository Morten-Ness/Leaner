import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imJ_mul : (a * b).imJ = a.re * b.imJ - a.imI * b.imK + a.imJ * b.re + a.imK * b.imI := (QuaternionAlgebra.imJ_mul a b).trans <| by ring

