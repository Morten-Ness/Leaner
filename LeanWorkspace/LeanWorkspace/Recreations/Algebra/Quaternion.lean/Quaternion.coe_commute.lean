import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_commute : Commute (↑r) a := QuaternionAlgebra.coe_commute r a

