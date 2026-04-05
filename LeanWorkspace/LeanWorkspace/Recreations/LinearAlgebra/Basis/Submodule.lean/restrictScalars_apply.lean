import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]

variable [Algebra R S] [Module S M] [Module R M]

variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)

theorem restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Module.Basis.restrictScalars, Module.Basis.span_apply]

