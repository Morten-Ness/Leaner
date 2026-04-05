import Mathlib

variable {G : Type*}

variable [CommMagma G] {a : G}

theorem CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G := ⟨fun _ _ _ h => mul_right_cancel <| (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

