import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S := ext fun _ => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

