import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem imI_mul : (a * b).imI = a.re * b.imI + a.imI * b.re + a.imJ * b.imK - a.imK * b.imJ := (QuaternionAlgebra.imI_mul a b).trans <| by ring

