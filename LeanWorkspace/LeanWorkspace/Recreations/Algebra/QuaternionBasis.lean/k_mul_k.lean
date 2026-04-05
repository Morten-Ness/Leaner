import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem k_mul_k : q.k * q.k = -((c₁ * c₃) • (1 : A)) := by
  rw [← i_mul_j, mul_assoc, ← mul_assoc q.j _ _, j_mul_i, ← i_mul_j, ← mul_assoc, mul_sub, ←
    mul_assoc, i_mul_i, add_mul, smul_mul_assoc, one_mul, sub_mul, smul_mul_assoc, mul_smul_comm,
    smul_mul_assoc, mul_assoc, j_mul_j, add_mul, smul_mul_assoc, j_mul_j, smul_smul,
    smul_mul_assoc, mul_assoc, j_mul_j]
  linear_combination (norm := module)

