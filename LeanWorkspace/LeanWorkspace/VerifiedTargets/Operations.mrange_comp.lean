import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mrange_comp {O : Type*} [MulOneClass O] (f : N →* O) (g : M →* N) :
    MonoidHom.mrange (f.comp g) = (MonoidHom.mrange g).map f := SetLike.coe_injective <| Set.range_comp f _

