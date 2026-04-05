import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddGroup R]

theorem sub_re_self : a - a.re = a.im := QuaternionAlgebra.ext (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

