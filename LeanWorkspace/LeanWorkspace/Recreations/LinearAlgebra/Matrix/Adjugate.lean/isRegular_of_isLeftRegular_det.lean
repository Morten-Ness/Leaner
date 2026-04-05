import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem isRegular_of_isLeftRegular_det {A : Matrix n n α} (hA : IsLeftRegular A.det) :
    IsRegular A := by
  constructor
  · intro B C h
    refine hA.matrix ?_
    simp only at h ⊢
    rw [← Matrix.one_mul B, ← Matrix.one_mul C, ← Matrix.smul_mul, ← Matrix.smul_mul, ←
      Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, h]
  · intro B C (h : B * A = C * A)
    refine hA.matrix ?_
    simp only
    rw [← Matrix.mul_one B, ← Matrix.mul_one C, ← Matrix.mul_smul, ← Matrix.mul_smul, ←
      Matrix.mul_adjugate, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

