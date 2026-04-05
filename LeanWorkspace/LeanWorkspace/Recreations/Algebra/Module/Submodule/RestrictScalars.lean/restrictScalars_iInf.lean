import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_iInf {ι : Sort*} (s : ι → Submodule R M) :
    (iInf s).restrictScalars S = ⨅ i, Submodule.restrictScalars S (s i) := by
  ext; simp

