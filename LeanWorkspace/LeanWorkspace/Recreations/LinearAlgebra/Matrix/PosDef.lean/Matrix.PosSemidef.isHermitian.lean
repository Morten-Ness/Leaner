import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian := hM.1

