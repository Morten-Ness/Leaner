import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_smul_of_tower {α} [Monoid α] [MulAction α R] [IsScalarTower α R R]
    [SMulCommClass α R R] (c : α) (A : Matrix n n R) :
    Matrix.det (c • A) = c ^ Fintype.card n • Matrix.det A := by
  rw [← smul_one_smul R c A, Matrix.det_smul, smul_pow, one_pow, smul_mul_assoc, one_mul]

