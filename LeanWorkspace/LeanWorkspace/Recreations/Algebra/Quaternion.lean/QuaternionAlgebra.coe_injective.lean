import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Zero R]

theorem coe_injective : Function.Injective (coe : R → ℍ[R,c₁,c₂,c₃]) := fun _ _ h => congr_arg re h

