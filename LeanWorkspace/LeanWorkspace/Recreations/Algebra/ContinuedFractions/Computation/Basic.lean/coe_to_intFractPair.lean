import Mathlib

variable (K : Type*)

variable {β : Type*} [Coe K β]

theorem coe_to_intFractPair {b : ℤ} {fr : K} :
    (↑(GenContFract.IntFractPair.mk b fr) : GenContFract.IntFractPair β) = GenContFract.IntFractPair.mk b (↑fr : β) := rfl

