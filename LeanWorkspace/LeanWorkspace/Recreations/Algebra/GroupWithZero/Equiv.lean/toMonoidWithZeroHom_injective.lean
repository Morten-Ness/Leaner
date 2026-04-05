import Mathlib

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H]

theorem toMonoidWithZeroHom_injective (f : G ≃* H) :
    Function.Injective f.toMonoidWithZeroHom := f.injective

