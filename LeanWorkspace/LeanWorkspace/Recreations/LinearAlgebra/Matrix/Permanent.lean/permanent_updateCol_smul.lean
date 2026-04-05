import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_updateCol_smul (M : Matrix n n R) (j : n) (c : R) (u : n → R) :
    Matrix.permanent (updateCol M j <| c • u) = c * Matrix.permanent (updateCol M j u) := by
  simp only [Matrix.permanent, ← mul_prod_erase _ _ (mem_univ j), updateCol_self, Pi.smul_apply,
    smul_eq_mul, mul_sum, ← mul_assoc]
  congr 1 with p
  rw [Finset.prod_congr rfl (fun i hi ↦ ?_)]
  simp only [ne_eq, ne_of_mem_erase hi, not_false_eq_true, updateCol_ne]

