import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem mapEquiv_symm (f : R ≃⋆* S) : Unitary.mapEquiv f.symm = (Unitary.mapEquiv f).symm := rfl

