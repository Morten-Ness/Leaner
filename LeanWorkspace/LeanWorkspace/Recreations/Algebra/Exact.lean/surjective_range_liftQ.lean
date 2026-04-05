import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem surjective_range_liftQ (h : range f ≤ ker g) (hg : Function.Surjective g) :
    Function.Surjective ((range f).liftQ g h) := by
  intro x₃
  obtain ⟨x₂, rfl⟩ := hg x₃
  exact ⟨Submodule.Quotient.mk x₂, rfl⟩

