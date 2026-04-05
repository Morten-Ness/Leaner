import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_inl_sup_mrange_inr : MonoidHom.mrange (inl M N) ⊔ MonoidHom.mrange (inr M N) = ⊤ := by
  simp only [Submonoid.mrange_inl, Submonoid.mrange_inr, Submonoid.prod_bot_sup_bot_prod, Submonoid.top_prod_top]

