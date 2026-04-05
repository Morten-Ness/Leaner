import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem mapEquiv_trans (f : R ≃⋆* S) (g : S ≃⋆* T) :
    Unitary.mapEquiv (f.trans g) = (Unitary.mapEquiv f).trans (Unitary.mapEquiv g) := rfl

