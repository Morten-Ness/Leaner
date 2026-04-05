import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

theorem boundaryLE {k' : ι'} {j : ι} (hj : c'.Rel (e.f j) k') (hk' : ∀ i, e.f i ≠ k') :
    e.BoundaryLE j := by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj, c'.next_eq' hk]

