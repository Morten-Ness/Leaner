import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1 := by simp [QuaternionAlgebra.Basis.lift]

