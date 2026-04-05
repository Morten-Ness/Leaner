import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateRow_sum_aux (M : Matrix n n R) {j : n} (s : Finset n) (hj : j ∉ s) (c : n → R)
    (a : R) :
    (M.updateRow j (a • M j + ∑ k ∈ s, (c k) • M k)).det = a • M.det := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, add_zero, smul_eq_mul, Matrix.det_updateRow_smul, updateRow_eq_self]
  | insert k _ hk h_ind =>
      have h : k ≠ j := fun h ↦ (h ▸ hj) (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert hk, add_comm ((c k) • M k), ← add_assoc, Matrix.det_updateRow_add,
        Matrix.det_updateRow_smul, Matrix.det_updateRow_eq_zero h, mul_zero, add_zero, h_ind]
      exact fun h ↦ hj (Finset.mem_insert_of_mem h)

