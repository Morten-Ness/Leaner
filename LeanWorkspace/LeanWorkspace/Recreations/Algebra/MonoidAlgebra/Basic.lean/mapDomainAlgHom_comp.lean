import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainAlgHom_comp (f : M →* N) (g : N →* O) :
    MonoidAlgebra.mapDomainAlgHom R A (g.comp f) = (MonoidAlgebra.mapDomainAlgHom R A g).comp (MonoidAlgebra.mapDomainAlgHom R A f) := by
  ext; simp [mapDomain_comp]

