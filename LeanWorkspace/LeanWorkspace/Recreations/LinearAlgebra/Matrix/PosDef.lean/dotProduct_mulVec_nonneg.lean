import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

theorem dotProduct_mulVec_nonneg {M : Matrix n n R} (hM : M.PosSemidef) :
    ∀ x : n → R, 0 ≤ star x ⬝ᵥ (M *ᵥ x) := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hM).2

