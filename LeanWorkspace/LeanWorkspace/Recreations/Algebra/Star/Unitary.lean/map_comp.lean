import Mathlib

variable {R : Type*}

variable {R S T : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [Monoid T] [StarMul T]

theorem map_comp (g : S →⋆* T) (f : R →⋆* S) : Unitary.map (g.comp f) = (Unitary.map g).comp (Unitary.map f) := rfl

