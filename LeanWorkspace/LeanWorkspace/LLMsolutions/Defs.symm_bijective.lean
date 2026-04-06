import Mathlib

variable {F α β M N P G H : Type*}

variable [EquivLike F α β]

variable [Mul M] [Mul N] [Mul P]

theorem symm_bijective : Function.Bijective (MulEquiv.symm : (M ≃* N) → N ≃* M) :=
by
  constructor
  · intro f g h
    have := congrArg MulEquiv.symm h
    simpa using this
  · intro f
    refine ⟨f.symm, ?_⟩
    rfl
