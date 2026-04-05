import Mathlib

variable {R : Type*} [Semiring R]

variable {l m n : Type*}

variable [Fintype m]

theorem Matrix.vecMul_injective_iff {M : Matrix m n R} :
    Function.Injective M.vecMul ↔ LinearIndependent R M.row := by
  rw [← coe_vecMulLinear, linearIndependent_iff_injective_fintypeLinearCombination]
  congr! 1
  exact funext fun _ => Matrix.vecMul_eq_sum _ _

