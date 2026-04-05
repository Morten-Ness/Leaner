import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem one_fromCols_isTotallyUnimodular_iff [DecidableEq m] (A : Matrix m n R) :
    (fromCols (1 : Matrix m m R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  rw [← Matrix.transpose_isTotallyUnimodular_iff, transpose_fromCols, transpose_one,
    Matrix.one_fromRows_isTotallyUnimodular_iff, Matrix.transpose_isTotallyUnimodular_iff]

alias ⟨_, Matrix.IsTotallyUnimodular.fromRows_one⟩ := Matrix.fromRows_one_isTotallyUnimodular_iff
alias ⟨_, Matrix.IsTotallyUnimodular.one_fromRows⟩ := Matrix.one_fromRows_isTotallyUnimodular_iff
alias ⟨_, Matrix.IsTotallyUnimodular.fromCols_one⟩ := Matrix.fromCols_one_isTotallyUnimodular_iff
alias ⟨_, Matrix.IsTotallyUnimodular.one_fromCols⟩ := one_fromCols_isTotallyUnimodular_iff

