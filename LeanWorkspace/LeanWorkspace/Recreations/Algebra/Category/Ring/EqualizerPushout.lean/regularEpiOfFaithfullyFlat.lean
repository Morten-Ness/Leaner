import Mathlib

variable {R S : CommRingCat.{u}ᵒᵖ} (f : S ⟶ R)

theorem regularEpiOfFaithfullyFlat (hf : f.unop.hom.FaithfullyFlat) :
    IsRegularEpi f := (isRegularEpi_op_iff_isRegularMono _).mpr (CommRingCat.isRegularMono_of_faithfullyFlat _ hf)

