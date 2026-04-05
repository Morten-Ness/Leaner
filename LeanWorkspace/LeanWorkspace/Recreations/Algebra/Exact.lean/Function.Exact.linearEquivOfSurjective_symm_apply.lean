import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem Function.Exact.linearEquivOfSurjective_symm_apply (h : Function.Exact f g)
    (hg : Function.Surjective g) (x : N) :
    (h.linearEquivOfSurjective hg).symm (g x) = Submodule.Quotient.mk x := by
  simp [LinearEquiv.symm_apply_eq]

