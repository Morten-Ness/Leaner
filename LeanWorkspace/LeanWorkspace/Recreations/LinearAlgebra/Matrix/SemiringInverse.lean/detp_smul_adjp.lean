import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem detp_smul_adjp (hAB : A * B = 1) :
    A + (Matrix.detp 1 A • Matrix.adjp (-1) B + Matrix.detp (-1) A • Matrix.adjp 1 B) =
      Matrix.detp 1 A • Matrix.adjp 1 B + Matrix.detp (-1) A • Matrix.adjp (-1) B := by
  have h0 := Matrix.detp_mul A B
  rw [hAB, Matrix.detp_one_one, Matrix.detp_neg_one_one, zero_add] at h0
  have h := Matrix.detp_smul_add_adjp hAB
  replace h := congr(Matrix.detp 1 A • $h + Matrix.detp (-1) A • $h.symm)
  simp only [smul_add, smul_smul] at h
  rwa [add_add_add_comm, ← add_smul, add_add_add_comm, ← add_smul, ← h0, add_smul, one_smul,
    add_comm A, add_assoc, ((Matrix.isAddUnit_detp_mul_detp hAB).smul_right _).add_right_inj] at h

