import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem bot_prod_bot : (⊥ : Submonoid M).prod (⊥ : Submonoid N) = ⊥ := SetLike.coe_injective <| by simp [Submonoid.coe_prod]

