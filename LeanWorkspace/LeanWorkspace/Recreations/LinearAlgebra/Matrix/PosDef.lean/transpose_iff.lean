import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem transpose_iff {M : Matrix n n R'} : Mᵀ.PosDef ↔ M.PosDef := ⟨(by simpa using ·.transpose), .transpose⟩

