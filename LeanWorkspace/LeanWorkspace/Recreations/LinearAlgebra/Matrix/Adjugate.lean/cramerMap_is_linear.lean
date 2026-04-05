import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramerMap_is_linear (i : n) : IsLinearMap α fun b => Matrix.cramerMap A b i := { map_add := det_updateCol_add _ _
    map_smul := det_updateCol_smul _ _ }

