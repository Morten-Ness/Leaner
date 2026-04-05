import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem coeff_eq_ncoeff (A : VertexOperator R V)
    (n : ℤ) : HVertexOperator.coeff A n = A[[-n - 1]] := by
  rw [VertexOperator.ncoeff_apply, neg_sub, Int.sub_neg, add_sub_cancel_left]

