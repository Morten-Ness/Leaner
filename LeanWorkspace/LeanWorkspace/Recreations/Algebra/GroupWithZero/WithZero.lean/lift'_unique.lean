import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulZeroOneClass β]

theorem lift'_unique (f : WithZero α →*₀ β) : f = lift' (f.toMonoidHom.comp WithZero.coeMonoidHom) := (lift'.apply_symm_apply f).symm

