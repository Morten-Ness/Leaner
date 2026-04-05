import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem ext : a.re = b.re → a.imI = b.imI → a.imJ = b.imJ → a.imK = b.imK → a = b := QuaternionAlgebra.ext

