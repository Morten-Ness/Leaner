import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddGroup R]

theorem sub_im_self : a - a.im = a.re := QuaternionAlgebra.ext (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

