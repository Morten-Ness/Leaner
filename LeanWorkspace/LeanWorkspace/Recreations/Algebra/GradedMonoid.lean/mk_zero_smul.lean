import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

variable [AddZeroClass ι] [GMul A]

theorem mk_zero_smul {i} (a : A 0) (b : A i) : GradedMonoid.mk _ (a • b) = GradedMonoid.mk _ a * GradedMonoid.mk _ b := Sigma.ext (zero_add _).symm <| eqRec_heq _ _

