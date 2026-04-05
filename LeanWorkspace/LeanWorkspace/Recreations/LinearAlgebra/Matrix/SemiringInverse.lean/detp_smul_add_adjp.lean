import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem detp_smul_add_adjp (hAB : A * B = 1) :
    Matrix.detp 1 B • A + Matrix.adjp (-1) B = Matrix.detp (-1) B • A + Matrix.adjp 1 B := by
  have key := congr(A * $(Matrix.mul_adjp_add_detp B))
  simp_rw [mul_add, ← mul_assoc, hAB, one_mul, mul_smul, mul_one] at key
  rwa [add_comm, eq_comm, add_comm]

