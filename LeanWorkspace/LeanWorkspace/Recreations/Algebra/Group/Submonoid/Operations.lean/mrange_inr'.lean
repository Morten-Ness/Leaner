import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_inr' : MonoidHom.mrange (inr M N) = Submonoid.comap (fst M N) ⊥ := Submonoid.mrange_inr.trans (Submonoid.prod_top _)

