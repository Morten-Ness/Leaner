import Mathlib

open scoped Matrix

variable {l m n α : Type*}

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

theorem det_one_add_mul_comm (A : Matrix m n α) (B : Matrix n m α) :
    det (1 + A * B) = det (1 + B * A) := calc
    det (1 + A * B) = det (fromBlocks 1 (-A) B 1) := by
      rw [Matrix.det_fromBlocks_one₂₂, Matrix.neg_mul, sub_neg_eq_add]
    _ = det (1 + B * A) := by rw [Matrix.det_fromBlocks_one₁₁, Matrix.mul_neg, sub_neg_eq_add]

