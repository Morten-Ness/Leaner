import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem mk_coe (e : α ≃+*o β) (h) : (⟨e, h⟩ : α ≃+*o β) = e := OrderRingIso.ext fun _ => rfl

