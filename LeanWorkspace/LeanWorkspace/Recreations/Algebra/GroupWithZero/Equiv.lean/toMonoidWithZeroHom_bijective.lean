import Mathlib

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H]

theorem toMonoidWithZeroHom_bijective (f : G ≃* H) :
    Function.Bijective f.toMonoidWithZeroHom := f.bijective

