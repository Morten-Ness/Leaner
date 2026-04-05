import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]

theorem _root_.Matrix.posDef_inv_iff [DecidableEq n] {M : Matrix n n K} :
    M⁻¹.PosDef ↔ M.PosDef := ⟨fun h =>
    letI := (Matrix.isUnit_nonsing_inv_iff.1 <| Matrix.PosDef.isUnit h).invertible
    Matrix.inv_inv_of_invertible M ▸ Matrix.PosDef.inv h, (·.inv)⟩

