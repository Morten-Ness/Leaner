import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_smul' [Monoid S] [DistribMulAction S R] (s : S) (a : ℍ[R,c₁,0,c₃]) :
    star (s • a) = s • star a := QuaternionAlgebra.ext (by simp) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

