import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem isUnit_nonsing_inv_iff {A : Matrix n n α} : IsUnit A⁻¹ ↔ IsUnit A := by
  simp_rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_nonsing_inv_det_iff]

-- `IsUnit.invertible` lifts the proposition `IsUnit A` to a constructive inverse of `A`.

