import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

theorem dotProduct_mulVec_pos {M : Matrix n n R} (hM : M.PosDef) {x} (hx : x ≠ 0) :
    0 < star x ⬝ᵥ (M *ᵥ x) := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx

