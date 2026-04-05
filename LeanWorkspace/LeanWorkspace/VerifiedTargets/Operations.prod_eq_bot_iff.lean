import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem prod_eq_bot_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊥ ↔ s = ⊥ ∧ t = ⊥ := by
  simp only [eq_bot_iff, Submonoid.prod_le_iff, (Submonoid.gc_map_comap _).le_iff_le, MonoidHom.comap_bot', MonoidHom.mker_inl, MonoidHom.mker_inr]

