import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulZeroOneClass β]

theorem monoidWithZeroHom_ext ⦃f g : WithZero α →*₀ β⦄
    (h : f.toMonoidHom.comp WithZero.coeMonoidHom = g.toMonoidHom.comp WithZero.coeMonoidHom) :
    f = g := DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

