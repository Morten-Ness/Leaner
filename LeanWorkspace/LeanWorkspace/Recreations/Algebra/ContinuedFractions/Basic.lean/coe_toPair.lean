import Mathlib

variable (α : Type*)

variable {β : Type*} [Coe α β]

theorem coe_toPair {a b : α} : (↑(GenContFract.Pair.mk a b) : GenContFract.Pair β) = GenContFract.Pair.mk (a : β) (b : β) := rfl

