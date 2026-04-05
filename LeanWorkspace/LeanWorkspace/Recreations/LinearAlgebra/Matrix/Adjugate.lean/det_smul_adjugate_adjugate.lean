import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem det_smul_adjugate_adjugate (A : Matrix n n α) :
    det A • Matrix.adjugate (Matrix.adjugate A) = det A ^ (Fintype.card n - 1) • A := by
  have : A * (A.adjugate * A.adjugate.adjugate) =
      A * (A.det ^ (Fintype.card n - 1) • (1 : Matrix n n α)) := by
    rw [← Matrix.adjugate_mul_distrib, Matrix.adjugate_mul, Matrix.adjugate_smul, Matrix.adjugate_one]
  rwa [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.one_mul] at this

