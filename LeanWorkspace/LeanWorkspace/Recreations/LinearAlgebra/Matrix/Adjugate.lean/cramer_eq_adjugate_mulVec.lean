import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem cramer_eq_adjugate_mulVec (A : Matrix n n α) (b : n → α) :
    Matrix.cramer A b = A.adjugate *ᵥ b := by
  nth_rw 2 [← A.transpose_transpose]
  rw [← Matrix.adjugate_transpose, Matrix.adjugate_def]
  have : b = ∑ i, b i • (Pi.single i 1 : n → α) := by
    refine (pi_eq_sum_univ b).trans ?_
    congr with j
    simp [Pi.single_apply, eq_comm]
  conv_lhs =>
    rw [this]
  ext k
  simp [mulVec, dotProduct, mul_comm]

