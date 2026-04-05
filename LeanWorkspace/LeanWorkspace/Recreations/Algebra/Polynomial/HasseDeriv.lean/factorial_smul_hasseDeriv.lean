import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem factorial_smul_hasseDeriv : ⇑(k ! • @Polynomial.hasseDeriv R _ k) = (@derivative R _)^[k] := by
  induction k with
  | zero => rw [Polynomial.hasseDeriv_zero, factorial_zero, iterate_zero, one_smul, LinearMap.id_coe]
  | succ k ih => ?_
  ext f n : 2
  rw [iterate_succ_apply', ← ih]
  simp only [LinearMap.smul_apply, coeff_smul, LinearMap.map_smul_of_tower, coeff_derivative,
    Polynomial.hasseDeriv_coeff, ← @choose_symm_add _ k]
  simp only [nsmul_eq_mul, factorial_succ, mul_assoc, succ_eq_add_one, ← add_assoc,
    add_right_comm n 1 k, ← cast_succ]
  rw [← (cast_commute (n + 1) (f.coeff (n + k + 1))).eq]
  simp only [← mul_assoc]
  norm_cast
  congr 2
  rw [mul_comm (k + 1) _, mul_assoc, mul_assoc]
  congr 1
  have : n + k + 1 = n + (k + 1) := by apply add_assoc
  rw [← choose_symm_of_eq_add this, choose_succ_right_eq, mul_comm]
  congr
  rw [add_assoc, add_tsub_cancel_left]

