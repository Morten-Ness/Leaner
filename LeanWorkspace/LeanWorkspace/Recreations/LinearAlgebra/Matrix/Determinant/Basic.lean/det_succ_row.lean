import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_succ_row {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    Matrix.det A =
      ∑ j : Fin n.succ, (-1) ^ (i + j : ℕ) * A i j * Matrix.det (A.submatrix i.succAbove j.succAbove) := by
  simp_rw [pow_add, mul_assoc, ← mul_sum]
  have : Matrix.det A = (-1 : R) ^ (i : ℕ) * (Perm.sign i.cycleRange⁻¹) * Matrix.det A := by
    calc
      Matrix.det A = ↑((-1 : ℤˣ) ^ (i : ℕ) * (-1 : ℤˣ) ^ (i : ℕ) : ℤˣ) * Matrix.det A := by simp
      _ = (-1 : R) ^ (i : ℕ) * (Perm.sign i.cycleRange⁻¹) * Matrix.det A := by simp [-Int.units_mul_self]
  rw [this, mul_assoc]
  congr
  rw [← Matrix.det_permute, Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, Matrix.submatrix_apply, submatrix_submatrix, id_comp, Function.comp_def, id]
  simp

