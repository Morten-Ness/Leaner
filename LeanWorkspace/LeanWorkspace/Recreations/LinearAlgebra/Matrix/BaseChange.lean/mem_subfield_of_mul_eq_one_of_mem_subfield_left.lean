import Mathlib

variable {m n L : Type*} [Finite m] [Fintype n] [DecidableEq m] [Field L]
  (e : m ≃ n) (K : Subfield L) {A : Matrix m n L} {B : Matrix n m L} (hAB : A * B = 1)

theorem mem_subfield_of_mul_eq_one_of_mem_subfield_left
    (h_mem : ∀ i j, B i j ∈ K) (i : m) (j : n) :
    A i j ∈ K := by
  replace hAB : Bᵀ * Aᵀ = 1 := by simpa using congr_arg transpose hAB
  rw [← A.transpose_apply]
  simp_rw [← B.transpose_apply] at h_mem
  exact Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_right e K hAB (fun i j ↦ h_mem j i) j i

