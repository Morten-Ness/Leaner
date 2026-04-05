import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem eq_bot_iff_forall : S = ⊥ ↔ ∀ x ∈ S, x = (1 : M) := SetLike.ext_iff.trans <| by simp +contextual [iff_def, S.one_mem]

