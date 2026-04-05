import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_sInf (s : Set (Submodule R M)) :
    (sInf s).restrictScalars S = sInf (Submodule.restrictScalars S '' s) := by
  ext; simp

