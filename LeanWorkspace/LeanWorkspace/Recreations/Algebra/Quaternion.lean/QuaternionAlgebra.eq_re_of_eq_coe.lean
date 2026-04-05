import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem eq_re_of_eq_coe {a : ℍ[R,c₁,c₂,c₃]} {x : R} (h : a = x) : a = a.re := by rw [h, QuaternionAlgebra.re_coe]

