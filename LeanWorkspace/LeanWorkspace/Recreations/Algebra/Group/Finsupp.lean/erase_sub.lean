import Mathlib

variable {ι F M N O G H : Type*}

variable [AddGroup G] {p : ι → Prop} {v v' : ι →₀ G}

theorem erase_sub (a : ι) (f₁ f₂ : ι →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ := (Finsupp.eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂

