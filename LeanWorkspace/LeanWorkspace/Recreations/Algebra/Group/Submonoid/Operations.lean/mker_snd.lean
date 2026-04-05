import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {F : Type*} [FunLike F M N] [mc : MonoidHomClass F M N]

theorem mker_snd : MonoidHom.mker (snd M N) = .prod ⊤ ⊥ := SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

