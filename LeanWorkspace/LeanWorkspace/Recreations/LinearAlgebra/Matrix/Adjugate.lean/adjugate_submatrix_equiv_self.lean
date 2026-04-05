import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_submatrix_equiv_self (e : n ≃ m) (A : Matrix m m α) :
    Matrix.adjugate (A.submatrix e e) = (Matrix.adjugate A).submatrix e e := by
  ext i j
  have : (fun j ↦ Pi.single i 1 <| e.symm j) = Pi.single (e i) 1 :=
    Function.update_comp_equiv (0 : n → α) e.symm i 1
  rw [Matrix.adjugate_apply, submatrix_apply, Matrix.adjugate_apply, ← det_submatrix_equiv_self e,
    updateRow_submatrix_equiv, this]

