import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem lift_add (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x + y) = q.lift x + q.lift y := by
  simp only [QuaternionAlgebra.Basis.lift, re_add, map_add, imI_add, add_smul, imJ_add, imK_add]
  abel

