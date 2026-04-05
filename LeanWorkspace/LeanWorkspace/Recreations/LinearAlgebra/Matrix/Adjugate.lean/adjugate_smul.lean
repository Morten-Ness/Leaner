import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_smul (r : α) (A : Matrix n n α) :
    Matrix.adjugate (r • A) = r ^ (Fintype.card n - 1) • Matrix.adjugate A := by
  rw [Matrix.adjugate, Matrix.adjugate, transpose_smul, Matrix.cramer_smul]
  rfl

