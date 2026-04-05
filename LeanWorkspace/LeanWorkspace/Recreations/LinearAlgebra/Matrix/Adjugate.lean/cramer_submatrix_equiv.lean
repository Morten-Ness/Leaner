import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_submatrix_equiv (A : Matrix m m α) (e : n ≃ m) (b : n → α) :
    Matrix.cramer (A.submatrix e e) b = Matrix.cramer A (b ∘ e.symm) ∘ e := by
  ext i
  simp_rw [Function.comp_apply, Matrix.cramer_apply, updateCol_submatrix_equiv,
    det_submatrix_equiv_self e, Function.comp_def]

