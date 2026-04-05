import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem trans_toRingEquiv_aux (f : α ≃+*o β) (g : β ≃+*o γ) :
    RingEquivClass.toRingEquiv (OrderRingIso.trans f g)
      = RingEquiv.trans f.toRingEquiv g.toRingEquiv := rfl

