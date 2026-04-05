import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem symm_bijective : Function.Bijective (RingEquiv.symm : (R ≃+* S) → S ≃+* R) := Function.bijective_iff_has_inverse.mpr ⟨_, RingEquiv.symm_symm, RingEquiv.symm_symm⟩

