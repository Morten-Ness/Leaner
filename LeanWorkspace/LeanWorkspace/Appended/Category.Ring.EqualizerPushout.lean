import Mathlib

section

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

theorem effectiveEpi_of_faithfullyFlat (hf : f.unop.hom.FaithfullyFlat) : EffectiveEpi f := (isRegularEpi_iff_effectiveEpi _).mp (CommRingCat.Opposite.regularEpiOfFaithfullyFlat _ hf)

end

section

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

theorem isRegularMono_of_faithfullyFlat (hf : f.hom.FaithfullyFlat) :
    IsRegularMono f := isRegularMono_of_regularMono (CommRingCat.regularMonoOfFaithfullyFlat f hf)

end

section

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

theorem regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
    IsRegularEpi f := (isRegularEpi_op_iff_isRegularMono _).mpr (CommRingCat.isRegularMono_of_faithfullyFlat _ hf)

end
