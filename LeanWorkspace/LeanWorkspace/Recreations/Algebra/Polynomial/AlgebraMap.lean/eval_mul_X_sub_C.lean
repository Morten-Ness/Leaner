import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [Ring R]

theorem eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (Polynomial.X - Polynomial.C r)).eval r = 0 := by
  simp only [eval, eval₂_eq_sum, RingHom.id_apply]
  have bound :=
    calc
      (p * (Polynomial.X - Polynomial.C r)).natDegree ≤ p.natDegree + (Polynomial.X - Polynomial.C r).natDegree := natDegree_mul_le
      _ ≤ p.natDegree + 1 := by grw [natDegree_X_sub_C_le]
      _ < p.natDegree + 2 := lt_add_one _
  rw [sum_over_range' _ _ (p.natDegree + 2) bound]
  swap
  · simp
  rw [sum_range_succ']
  conv_lhs =>
    congr
    arg 2
    simp [coeff_mul_X_sub_C, sub_mul, mul_assoc, ← pow_succ']
  rw [sum_range_sub']
  simp

