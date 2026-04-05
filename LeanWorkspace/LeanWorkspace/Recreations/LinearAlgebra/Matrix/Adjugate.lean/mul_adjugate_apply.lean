import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem mul_adjugate_apply (A : Matrix n n α) (i j k) :
    A i k * Matrix.adjugate A k j = Matrix.cramer Aᵀ (Pi.single k (A i k)) j := by
  rw [← smul_eq_mul, Matrix.adjugate, of_apply, ← Pi.smul_apply, ← map_smul, ← Pi.single_smul',
    smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in

