import Mathlib

variable {R : Type*} [Ring R] {n : Type*} [Fintype n] [DecidableEq n]

theorem single_mem_jacobson_matrix (I : Ideal R) :
    ∀ x ∈ I.jacobson, ∀ (i j : n), single i j x ∈ (I.matrix n).jacobson := by
  -- Proof generalized from example 8 in
  -- https://ysharifi.wordpress.com/2022/08/16/the-jacobson-radical-basic-examples/
  simp_rw [Ideal.mem_jacobson_iff]
  intro x xIJ p q M
  have ⟨z, zMx⟩ := xIJ (M q p)
  let N : Matrix n n R := 1 - ∑ i, single i q (if i = q then 1 - z else (M i p) * x * z)
  use N
  intro i j
  obtain rfl | qj := eq_or_ne q j
  · by_cases iq : i = q
    · simp [iq, N, zMx, single, mul_apply, sum_apply, ite_and, sub_mul]
    · convert I.mul_mem_left (-M i p * x) zMx
      simp [iq, N, single, mul_apply, sum_apply, ite_and, sub_mul]
      simp [sub_add, mul_add, mul_sub, mul_assoc]
  · simp [N, qj, sum_apply, mul_apply]

