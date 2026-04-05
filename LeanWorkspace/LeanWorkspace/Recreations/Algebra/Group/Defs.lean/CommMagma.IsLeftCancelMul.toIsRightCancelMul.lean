import Mathlib

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G := ⟨fun _ _ _ h => mul_left_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

