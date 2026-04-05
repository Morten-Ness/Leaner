import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem toMonoidHom_mapEquiv (f : R ≃⋆* S) :
    (Unitary.mapEquiv f).toStarMonoidHom = Unitary.map f.toStarMonoidHom := rfl

