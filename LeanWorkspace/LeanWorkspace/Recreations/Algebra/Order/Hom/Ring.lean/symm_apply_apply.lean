import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem symm_apply_apply (e : α ≃+*o β) (a : α) : e.symm (e a) = a := e.toRingEquiv.symm_apply_apply a

