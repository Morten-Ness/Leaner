import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingHom_comp (f : S →+* T) (g : R →+* S) :
    MonoidAlgebra.mapRingHom M (f.comp g) = (MonoidAlgebra.mapRingHom M f).comp (MonoidAlgebra.mapRingHom M g) := by
  ext <;> simp

