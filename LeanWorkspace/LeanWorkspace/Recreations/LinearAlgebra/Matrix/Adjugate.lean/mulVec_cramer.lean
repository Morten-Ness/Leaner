import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem mulVec_cramer (A : Matrix n n α) (b : n → α) : A *ᵥ Matrix.cramer A b = A.det • b := by
  rw [Matrix.cramer_eq_adjugate_mulVec, mulVec_mulVec, Matrix.mul_adjugate, smul_mulVec, one_mulVec]

