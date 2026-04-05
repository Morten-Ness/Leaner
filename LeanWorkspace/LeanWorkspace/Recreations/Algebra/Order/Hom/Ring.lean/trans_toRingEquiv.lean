import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem trans_toRingEquiv (f : α ≃+*o β) (g : β ≃+*o γ) :
    (OrderRingIso.trans f g).toRingEquiv = RingEquiv.trans f.toRingEquiv g.toRingEquiv := rfl

