import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem star_smul [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R]) :
    star (s • a) = s • star a := QuaternionAlgebra.star_smul' s a

