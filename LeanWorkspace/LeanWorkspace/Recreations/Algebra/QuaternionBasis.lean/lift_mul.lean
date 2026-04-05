import Mathlib

variable {R : Type*} {A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable {c₁ c₂ c₃ : R}

variable (q : Basis A c₁ c₂ c₃)

theorem lift_mul (x y : ℍ[R,c₁,c₂,c₃]) : q.lift (x * y) = q.lift x * q.lift y := by
  simp only [QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one]
  simp_rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  simp only [i_mul_i, j_mul_j, i_mul_j, j_mul_i, QuaternionAlgebra.Basis.i_mul_k, QuaternionAlgebra.Basis.k_mul_i, QuaternionAlgebra.Basis.k_mul_j, QuaternionAlgebra.Basis.j_mul_k, QuaternionAlgebra.Basis.k_mul_k]
  simp only [smul_smul, smul_neg, sub_eq_add_neg, ← add_assoc, neg_smul]
  simp only [mul_right_comm _ _ (c₁ * c₃), mul_comm _ (c₁ * c₃)]
  simp only [mul_comm _ c₁]
  simp only [mul_right_comm _ _ c₃]
  simp only [← mul_assoc]
  simp only [re_mul, sub_eq_add_neg, add_smul, neg_smul, imI_mul, ← add_assoc, imJ_mul, imK_mul]
  linear_combination (norm := module)

