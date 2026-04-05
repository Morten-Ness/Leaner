import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_sSup (s : Set (Submodule R M)) :
    (sSup s).restrictScalars S = sSup (Submodule.restrictScalars S '' s) := by
  simp [← toAddSubmonoid_inj, toAddSubmonoid_sSup, ← Set.image_comp]

