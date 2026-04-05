import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef := ⟨hM.1, fun x ↦ by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩

