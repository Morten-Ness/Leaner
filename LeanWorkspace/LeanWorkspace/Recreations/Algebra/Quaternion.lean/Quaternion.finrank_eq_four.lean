import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem finrank_eq_four [StrongRankCondition R] : Module.finrank R ℍ[R] = 4 := QuaternionAlgebra.finrank_eq_four _ _ _

