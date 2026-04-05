import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapDomainNonUnitalRingHom_comp (f : N →ₙ* O) (g : M →ₙ* N) :
    MonoidAlgebra.mapDomainNonUnitalRingHom R (f.comp g) =
      (MonoidAlgebra.mapDomainNonUnitalRingHom R f).comp (MonoidAlgebra.mapDomainNonUnitalRingHom R g) := by
  ext; simp [Finsupp.mapDomain_comp]

