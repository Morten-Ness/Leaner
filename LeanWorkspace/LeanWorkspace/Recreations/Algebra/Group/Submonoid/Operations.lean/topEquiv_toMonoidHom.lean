import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem topEquiv_toMonoidHom : ((Submonoid.topEquiv : _ ≃* M) : _ →* M) = (⊤ : Submonoid M).subtype := rfl

