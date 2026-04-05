import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [AddGroup R]

theorem re_add_im : ↑a.re + a.im = a := QuaternionAlgebra.ext (add_zero _) (zero_add _) (zero_add _) (zero_add _)

