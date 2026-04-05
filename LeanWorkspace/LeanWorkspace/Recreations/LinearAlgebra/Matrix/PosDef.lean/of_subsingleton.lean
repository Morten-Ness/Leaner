import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem of_subsingleton (h : Subsingleton R) (M : Matrix n n R) : M.PosDef := ⟨.of_subsingleton, fun _ hx ↦ (hx <| Subsingleton.elim ..).elim⟩

