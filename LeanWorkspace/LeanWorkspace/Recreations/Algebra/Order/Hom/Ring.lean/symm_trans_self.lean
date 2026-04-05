import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem symm_trans_self (e : α ≃+*o β) : e.symm.trans e = OrderRingIso.refl β := OrderRingIso.ext e.right_inv

