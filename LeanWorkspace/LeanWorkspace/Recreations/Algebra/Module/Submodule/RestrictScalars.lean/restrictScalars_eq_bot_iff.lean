import Mathlib

variable (S : Type*) {R M : Type*} [Semiring R] [AddCommMonoid M] [Semiring S]
  [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]

theorem restrictScalars_eq_bot_iff {p : Submodule R M} : Submodule.restrictScalars S p = ⊥ ↔ p = ⊥ := by
  simp [SetLike.ext_iff]

