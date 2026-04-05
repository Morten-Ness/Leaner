import Mathlib

variable {F α β γ δ : Type*}

variable [Mul α] [Add α] [LE α] [Mul β] [Add β] [LE β] [Mul γ] [Add γ] [LE γ]

theorem ext {f g : α ≃+*o β} (h : ∀ a, f a = g a) : f = g := DFunLike.ext f g h

