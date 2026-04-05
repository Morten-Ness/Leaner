import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem star_add_self' : star a + a = ↑(2 * a.re) := by
  simpa using QuaternionAlgebra.star_add_self' a

