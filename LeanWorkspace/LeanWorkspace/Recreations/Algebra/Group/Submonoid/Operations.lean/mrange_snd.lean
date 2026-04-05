import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_snd : MonoidHom.mrange (snd M N) = ⊤ := MonoidHom.mrange_eq_top_of_surjective (snd M N) <| @Prod.snd_surjective _ _ ⟨1⟩

