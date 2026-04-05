import Mathlib

variable {ι : Type*} {σ S R : Type*}

variable [Ring R] [AddMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]

variable (A : ι → σ) [SetLike.GradedMonoid A]

theorem coe_intCast (z : ℤ) : (z : A 0) = (z : R) := rfl

