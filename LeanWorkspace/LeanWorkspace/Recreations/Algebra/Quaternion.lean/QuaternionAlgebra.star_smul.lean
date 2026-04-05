import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem star_smul [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (s : S) (a : ℍ[R,c₁,c₂,c₃]) :
    star (s • a) = s • star a := QuaternionAlgebra.ext
    (by simp [mul_smul_comm]) (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

