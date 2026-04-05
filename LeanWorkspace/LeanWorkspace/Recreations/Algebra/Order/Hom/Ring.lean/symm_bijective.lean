import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem symm_bijective : Function.Bijective (OrderRingIso.symm : (α ≃+*o β) → β ≃+*o α) := Function.bijective_iff_has_inverse.mpr ⟨_, OrderRingIso.symm_symm, OrderRingIso.symm_symm⟩

