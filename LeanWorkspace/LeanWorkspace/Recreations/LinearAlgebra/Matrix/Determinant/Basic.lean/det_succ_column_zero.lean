import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_succ_column_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
    Matrix.det A = ∑ i : Fin n.succ, (-1) ^ (i : ℕ) * A i 0 * Matrix.det (A.submatrix i.succAbove Fin.succ) := by
  rw [Matrix.det_apply, Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product, Matrix.submatrix]
  refine Finset.sum_congr rfl fun i _ => Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.prod_univ_succ, Matrix.det_apply, Finset.mul_sum,
      Equiv.Perm.decomposeFin_symm_apply_zero, Fin.val_zero, one_mul,
      Equiv.Perm.decomposeFin.symm_sign, Equiv.swap_self, if_true, id,
      Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succAbove_zero, Equiv.coe_refl, pow_zero,
      mul_smul_comm, of_apply]
  -- `univ_perm_fin_succ` gives a different embedding of `Perm (Fin n)` into
  -- `Perm (Fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = (Perm.sign i.cycleRange) := by simp [Fin.sign_cycleRange]
  rw [Fin.val_succ, pow_succ', this, mul_assoc, mul_assoc, mul_left_comm (ε _),
    ← Matrix.det_permute, Matrix.det_apply, Finset.mul_sum, Finset.mul_sum]
  -- now we just need to move the corresponding parts to the same place
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Equiv.Perm.decomposeFin.symm_sign, if_neg (Fin.succ_ne_zero i)]
  calc
    ((-1 * Perm.sign σ : ℤ) • ∏ i', A (Perm.decomposeFin.symm (Fin.succ i, σ) i') i') =
        (-1 * Perm.sign σ : ℤ) • (A (Fin.succ i) 0 *
          ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp only [Fin.prod_univ_succ, Fin.succAbove_cycleRange,
        Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
    _ = -1 * (A (Fin.succ i) 0 * (Perm.sign σ : ℤ) •
        ∏ i', A ((Fin.succ i).succAbove (Fin.cycleRange i (σ i'))) i'.succ) := by
      simp [_root_.neg_mul, one_mul, zsmul_eq_mul, neg_smul,
        Fin.succAbove_cycleRange, mul_left_comm]

