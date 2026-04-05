import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem toUnits_comp_map (f : R →⋆* S) :
    Unitary.toUnits.comp (Unitary.map f).toMonoidHom = (Units.map f.toMonoidHom).comp Unitary.toUnits := by
  ext; rfl

