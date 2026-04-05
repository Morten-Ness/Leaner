import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_inl : MonoidHom.mrange (inl M N) = Submonoid.prod ⊤ ⊥ := by simpa only [MonoidHom.mrange_eq_map] using Submonoid.map_inl ⊤

