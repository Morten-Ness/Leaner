import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem star_eq_two_re_sub : star a = ↑(2 * a.re) - a := by
  simpa using QuaternionAlgebra.star_eq_two_re_sub a

