import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem top_prod (s : Submonoid N) : (⊤ : Submonoid M).prod s = s.comap (MonoidHom.snd M N) := ext fun x => by simp [Submonoid.mem_prod, MonoidHom.coe_snd]

