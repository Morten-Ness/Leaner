import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_smul (r : α) (A : Matrix n n α) :
    Matrix.cramer (r • A) = r ^ (Fintype.card n - 1) • Matrix.cramer A := LinearMap.ext fun _ => funext fun _ => det_updateCol_smul_left _ _ _ _

