import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mker_prod_map {M' : Type*} {N' : Type*} [MulOneClass M'] [MulOneClass N'] (f : M →* N)
    (g : M' →* N') : MonoidHom.mker (prodMap f g) = (MonoidHom.mker f).prod (MonoidHom.mker g) := by
  rw [← MonoidHom.comap_bot', ← MonoidHom.comap_bot', ← MonoidHom.comap_bot', ← MonoidHom.prod_map_comap_prod', Submonoid.bot_prod_bot]

