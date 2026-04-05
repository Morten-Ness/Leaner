import Mathlib

open scoped Ring

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem det_nonsing_inv : A⁻¹.det = A.det⁻¹ʳ := by
  by_cases h : IsUnit A.det
  · cases h.nonempty_invertible
    letI := Matrix.invertibleOfDetInvertible A
    rw [Ring.inverse_invertible, ← Matrix.invOf_eq_nonsing_inv, Matrix.det_invOf]
  cases isEmpty_or_nonempty n
  · rw [det_isEmpty, det_isEmpty, Ring.inverse_one]
  · rw [Ring.inverse_non_unit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h, det_zero ‹_›]

