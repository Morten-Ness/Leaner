import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem apply_symm_apply (e : α ≃+*o β) (b : β) : e (e.symm b) = b := e.toRingEquiv.apply_symm_apply b

