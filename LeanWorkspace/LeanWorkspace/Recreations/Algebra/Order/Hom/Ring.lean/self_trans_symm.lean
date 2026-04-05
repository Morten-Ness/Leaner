import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem self_trans_symm (e : α ≃+*o β) : e.trans e.symm = OrderRingIso.refl α := OrderRingIso.ext e.left_inv

