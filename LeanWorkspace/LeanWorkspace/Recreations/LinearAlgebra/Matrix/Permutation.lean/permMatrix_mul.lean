import Mathlib

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

theorem permMatrix_mul [NonAssocSemiring R] :
    (σ * τ).permMatrix R = τ.permMatrix R * σ.permMatrix R := by
  rw [Equiv.Perm.permMatrix, Equiv.Perm.mul_def, toPEquiv_trans, PEquiv.toMatrix_trans]

