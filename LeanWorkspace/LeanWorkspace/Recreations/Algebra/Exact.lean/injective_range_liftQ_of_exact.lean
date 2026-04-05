import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem injective_range_liftQ_of_exact (h : Function.Exact f g) :
    Function.Injective ((range f).liftQ g (h · |>.mpr)) := by
  simpa only [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot_range_liftQ_iff, LinearMap.exact_iff] using h

