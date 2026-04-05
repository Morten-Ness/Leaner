import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem symm_symm (e : α ≃+*o β) : e.symm.symm = e := rfl

