import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem j_mul_k : q.j * q.k = (c₂ * c₃) • 1 - c₃ • q.i := by
  rw [← i_mul_j, ← mul_assoc, j_mul_i, sub_mul, smul_mul_assoc, j_mul_j, ← smul_assoc, QuaternionAlgebra.Basis.k_mul_j]
  rfl

