import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem transpose {M : Matrix n n R'} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM.2 (Finsupp.mapRange star (star_zero R') x)

