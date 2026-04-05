import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_inl' : MonoidHom.mrange (inl M N) = Submonoid.comap (snd M N) ⊥ := Submonoid.mrange_inl.trans (Submonoid.top_prod _)

