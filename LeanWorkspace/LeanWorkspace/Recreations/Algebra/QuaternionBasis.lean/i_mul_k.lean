import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem i_mul_k : q.i * q.k = c₁ • q.j + c₂ • q.k := by
  rw [← i_mul_j, ← mul_assoc, i_mul_i, add_mul, smul_mul_assoc, one_mul, smul_mul_assoc]

