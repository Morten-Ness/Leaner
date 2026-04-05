import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem im_star : (star a).im = -a.im := QuaternionAlgebra.ext neg_zero.symm rfl rfl rfl

