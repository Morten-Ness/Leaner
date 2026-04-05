import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem trans_apply (f : α ≃+*o β) (g : β ≃+*o γ) (a : α) : f.trans g a = g (f a) := rfl

