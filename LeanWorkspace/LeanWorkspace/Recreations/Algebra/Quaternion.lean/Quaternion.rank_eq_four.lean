import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem rank_eq_four [StrongRankCondition R] : Module.rank R ℍ[R] = 4 := QuaternionAlgebra.rank_eq_four _ _ _

