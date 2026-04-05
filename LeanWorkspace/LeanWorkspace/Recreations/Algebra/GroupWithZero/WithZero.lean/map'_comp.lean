import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_comp (f : α →* β) (g : β →* γ) : WithZero.map' (g.comp f) = (WithZero.map' g).comp (WithZero.map' f) := MonoidWithZeroHom.ext fun x => (WithZero.map'_map' f g x).symm

