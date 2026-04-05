import Mathlib

variable {ι : Type*} [DecidableEq ι]

variable (A : ι → Type*)

variable [Zero ι] [GradedMonoid.GOne A] [∀ i, AddCommMonoid (A i)]

theorem one_def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one := rfl

