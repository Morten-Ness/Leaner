import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem mrange_fst : MonoidHom.mrange (fst M N) = ⊤ := MonoidHom.mrange_eq_top_of_surjective (fst M N) <| @Prod.fst_surjective _ _ ⟨1⟩

