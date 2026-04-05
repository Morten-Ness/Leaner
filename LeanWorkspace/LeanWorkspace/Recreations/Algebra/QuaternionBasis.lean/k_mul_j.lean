import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem k_mul_j : q.k * q.j = c₃ • q.i := by
  rw [← i_mul_j, mul_assoc, j_mul_j, mul_smul_comm, mul_one]

