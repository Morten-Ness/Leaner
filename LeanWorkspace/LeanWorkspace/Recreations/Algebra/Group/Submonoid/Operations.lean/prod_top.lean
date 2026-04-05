import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

variable {M : Type*} [MulOneClass M] (S : Submonoid M)

theorem prod_top (s : Submonoid M) : s.prod (⊤ : Submonoid N) = s.comap (MonoidHom.fst M N) := ext fun x => by simp [Submonoid.mem_prod, MonoidHom.coe_fst]

