import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

theorem of_dotProduct_mulVec_pos {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x)) : M.PosDef := Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

