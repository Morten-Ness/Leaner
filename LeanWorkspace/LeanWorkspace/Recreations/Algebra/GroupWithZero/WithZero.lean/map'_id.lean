import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_id : WithZero.map' (MonoidHom.id β) = MonoidHom.id (WithZero β) := by
  ext x; induction x <;> rfl

