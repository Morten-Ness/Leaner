import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem lift_smul (r : R) (x : ℍ[R,c₁,c₂,c₃]) : q.lift (r • x) = r • q.lift x := by
  simp [QuaternionAlgebra.Basis.lift, mul_smul, ← Algebra.smul_def]

