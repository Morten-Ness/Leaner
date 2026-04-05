import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem transpose {M : Matrix n n R'} (hM : M.PosDef) : Mᵀ.PosDef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨Matrix.PosSemidef.transpose hM.1, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
      hM.2 (x := x.mapRange star (star_zero R'))

