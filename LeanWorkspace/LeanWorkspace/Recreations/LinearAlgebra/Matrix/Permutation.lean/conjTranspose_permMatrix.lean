import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

theorem conjTranspose_permMatrix [NonAssocSemiring R] [StarRing R] :
    (σ.permMatrix R).conjTranspose = (σ⁻¹).permMatrix R := by
  simp only [conjTranspose, Matrix.transpose_permMatrix, map]
  aesop

