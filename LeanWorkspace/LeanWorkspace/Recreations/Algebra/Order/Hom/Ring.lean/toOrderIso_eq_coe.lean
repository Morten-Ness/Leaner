import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem toOrderIso_eq_coe (f : α ≃+*o β) : f.toOrderIso = f := OrderIso.ext rfl

