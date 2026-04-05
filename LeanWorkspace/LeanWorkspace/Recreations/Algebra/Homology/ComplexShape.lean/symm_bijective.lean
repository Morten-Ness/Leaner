import Mathlib

variable {ι : Type*}

theorem symm_bijective :
    Function.Bijective (ComplexShape.symm : ComplexShape ι → ComplexShape ι) := Function.bijective_iff_has_inverse.mpr ⟨_, ComplexShape.symm_symm, ComplexShape.symm_symm⟩

