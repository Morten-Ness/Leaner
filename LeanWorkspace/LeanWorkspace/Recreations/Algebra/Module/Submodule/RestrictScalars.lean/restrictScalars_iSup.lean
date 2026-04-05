import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_iSup {ι : Sort*} (s : ι → Submodule R M) :
    (iSup s).restrictScalars S = ⨆ i, Submodule.restrictScalars S (s i) := map_iSup (Submodule.restrictScalarsLatticeHom S R M) s

