import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

variable [AddMonoid ι] [GMul A] [GOne A]

theorem gnpowRec_zero (a : GradedMonoid A) : GradedMonoid.mk _ (GradedMonoid.GMonoid.gnpowRec 0 a.snd) = 1 := Sigma.ext (zero_nsmul _) (heq_of_cast_eq _ rfl).symm

