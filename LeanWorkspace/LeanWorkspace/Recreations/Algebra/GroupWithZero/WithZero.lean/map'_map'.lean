import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_map' (f : α →* β) (g : β →* γ) (x) : WithZero.map' g (WithZero.map' f x) = WithZero.map' (g.comp f) x := by
  induction x <;> rfl

