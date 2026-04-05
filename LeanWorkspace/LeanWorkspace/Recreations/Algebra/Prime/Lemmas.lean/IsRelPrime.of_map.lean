import Mathlib

variable {M N : Type*}

theorem IsRelPrime.of_map
    {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [MulHomClass F M N]
    (f : F) [IsLocalHom f] {a b : M}
    (hab : IsRelPrime (f a) (f b)) : IsRelPrime a b := fun _ h₁ h₂ ↦ .of_map _ _ (hab (map_dvd f h₁) (map_dvd f h₂))

