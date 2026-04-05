import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem MulEquivClass.map_finprod {F : Type*} [EquivLike F M N] [MulEquivClass F M N] (g : F)
    (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) := MulEquiv.map_finprod (MulEquivClass.toMulEquiv g) f

