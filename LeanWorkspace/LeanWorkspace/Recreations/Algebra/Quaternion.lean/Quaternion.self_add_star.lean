import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem self_add_star : a + star a = 2 * a.re := by
  simpa using QuaternionAlgebra.self_add_star a

