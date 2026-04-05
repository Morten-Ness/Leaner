import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem bot_or_exists_ne_one (S : Submonoid M) : S = ⊥ ∨ ∃ x ∈ S, x ≠ (1 : M) := S.bot_or_nontrivial.imp_right S.nontrivial_iff_exists_ne_one.mp

