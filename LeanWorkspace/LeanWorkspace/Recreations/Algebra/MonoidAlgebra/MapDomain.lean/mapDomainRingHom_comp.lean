import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainRingHom_comp (f : N →* O) (g : M →* N) :
    MonoidAlgebra.mapDomainRingHom R (f.comp g) = (MonoidAlgebra.mapDomainRingHom R f).comp (MonoidAlgebra.mapDomainRingHom R g) := by
  ext <;> simp

