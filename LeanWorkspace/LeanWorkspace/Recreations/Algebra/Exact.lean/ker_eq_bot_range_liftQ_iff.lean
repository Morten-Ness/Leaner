import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}

theorem ker_eq_bot_range_liftQ_iff (h : range f ≤ ker g) :
    ker ((range f).liftQ g h) = ⊥ ↔ ker g = range f := by
  simp only [Submodule.ext_iff, mem_ker, Submodule.mem_bot, mem_range]
  constructor
  · intro hfg x
    simpa using hfg (Submodule.Quotient.mk x)
  · intro hfg x
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simpa using hfg x

