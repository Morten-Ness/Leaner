import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem bot_or_nontrivial (S : Submonoid M) : S = ⊥ ∨ Nontrivial S := by
  simp only [Submonoid.eq_bot_iff_forall, Submonoid.nontrivial_iff_exists_ne_one, ← not_forall, ← Classical.not_imp,
    Classical.em]

