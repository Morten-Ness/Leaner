import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_reindex (e e' : m ≃ n) (M : Matrix m m R) :
    (M.reindex e e').det = sign (e'.trans e.symm) * M.det := by
  trans ((M.reindex (e.trans e'.symm) (.refl _)).reindex e' e').det
  · congr 1; ext; simp
  · simp_rw [Matrix.det_reindex_self, reindex_apply, Equiv.refl_symm, Equiv.coe_refl, Matrix.det_permute]
    rfl

