import Mathlib

open scoped Nat

variable {R S : Type*}

variable [Semiring R] [Semiring S]

theorem exists_iterate_derivative_eq_factorial_smul (p : R[X]) (k : ℕ) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - k ∧ derivative^[k] p = k ! • gp := by
  refine ⟨_, (natDegree_sum_le _ _).trans ?_, iterate_derivative_eq_factorial_smul_sum p k⟩
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun i hi => ?_⟩
  dsimp only [Function.comp]
  exact (natDegree_C_mul_le _ _).trans <| (natDegree_X_pow_le _).trans <|
    (le_natDegree_of_mem_supp _ hi).trans <| natDegree_iterate_derivative _ _

