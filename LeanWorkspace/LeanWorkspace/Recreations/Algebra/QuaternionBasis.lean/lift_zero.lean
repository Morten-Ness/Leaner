import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem lift_zero : q.lift (0 : ℍ[R,c₁,c₂,c₃]) = 0 := by simp [QuaternionAlgebra.Basis.lift]

