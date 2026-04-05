import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem coe_toRingEquiv (f : α ≃+*o β) : ⇑(f : α ≃+* β) = f := rfl

