import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m → n) :
    (M.submatrix e e).PosSemidef := by
  refine ⟨hM.1.submatrix _, fun x ↦ ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 <| x.mapDomain e

