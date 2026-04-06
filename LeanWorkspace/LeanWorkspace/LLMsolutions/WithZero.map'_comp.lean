import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_comp (f : α →* β) (g : β →* γ) : WithZero.map' (g.comp f) = (WithZero.map' g).comp (WithZero.map' f) := by
  ext x <;> rfl
