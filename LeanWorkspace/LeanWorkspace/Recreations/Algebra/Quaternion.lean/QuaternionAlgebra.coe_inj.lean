import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Zero R]

theorem coe_inj {x y : R} : (x : ℍ[R,c₁,c₂,c₃]) = y ↔ x = y := QuaternionAlgebra.coe_injective.eq_iff

