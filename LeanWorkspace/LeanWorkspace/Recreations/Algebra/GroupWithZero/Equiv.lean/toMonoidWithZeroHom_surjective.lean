import Mathlib

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H]

theorem toMonoidWithZeroHom_surjective (f : G ≃* H) :
    Function.Surjective f.toMonoidWithZeroHom := f.surjective

