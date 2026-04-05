import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem diag_nonneg {A : Matrix n n R} (hA : A.PosSemidef) {i : n} : 0 ≤ A i i := by
  simpa using hA.2 <| .single i 1

