import Mathlib

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

theorem effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f := (isRegularEpi_iff_effectiveEpi _).mp (CommRingCat.Opposite.regularEpiOfFaithfullyFlat _ hf)

