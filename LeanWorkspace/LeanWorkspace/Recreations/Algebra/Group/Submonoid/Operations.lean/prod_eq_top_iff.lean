import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem prod_eq_top_iff {s : Submonoid M} {t : Submonoid N} : s.prod t = ⊤ ↔ s = ⊤ ∧ t = ⊤ := by
  simp only [eq_top_iff, Submonoid.le_prod_iff, ← MonoidHom.mrange_eq_map, Submonoid.mrange_fst, Submonoid.mrange_snd]

