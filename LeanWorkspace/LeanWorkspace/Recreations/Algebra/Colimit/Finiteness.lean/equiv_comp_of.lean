import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

variable [DecidableEq (Submodule R M)]

theorem equiv_comp_of (N : {N : Submodule R M // N.FG}) :
    (Module.fgSystem.equiv R M).toLinearMap ∘ₗ of _ _ _ _ N = N.1.subtype := by
  ext; simp [Module.fgSystem.equiv]

