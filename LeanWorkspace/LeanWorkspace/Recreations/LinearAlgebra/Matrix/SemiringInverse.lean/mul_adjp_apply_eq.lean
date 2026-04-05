import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem mul_adjp_apply_eq : (A * Matrix.adjp s A) i i = Matrix.detp s A := by
  have key := sum_fiberwise_eq_sum_filter (ofSign s) Finset.univ (· i) fun σ ↦ ∏ k, A k (σ k)
  simp_rw [mem_univ, filter_true] at key
  simp_rw [mul_apply, Matrix.adjp_apply, mul_sum, Matrix.detp, ← key]
  refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun σ hσ ↦ ?_
  rw [← prod_mul_prod_compl ({i} : Finset n), prod_singleton, (mem_filter.mp hσ).2]

