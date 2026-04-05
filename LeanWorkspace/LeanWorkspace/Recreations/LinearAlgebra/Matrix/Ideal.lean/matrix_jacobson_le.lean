import Mathlib

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_jacobson_le (I : Ideal R) :
    I.jacobson.matrix n ≤ (I.matrix n).jacobson := by
  intro M MI
  rw [matrix_eq_sum_single M]
  apply sum_mem
  intro i _
  apply sum_mem
  intro j _
  apply Ideal.single_mem_jacobson_matrix I _ (MI i j)

