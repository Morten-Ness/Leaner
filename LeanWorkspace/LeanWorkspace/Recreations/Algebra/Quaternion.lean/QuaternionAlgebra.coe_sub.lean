import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem coe_sub : ((x - y : R) : ℍ[R,c₁,c₂,c₃]) = x - y := (algebraMap R ℍ[R,c₁,c₂,c₃]).map_sub x y

