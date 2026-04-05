import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = (f : ℕ → α) ⊔ g := rfl

