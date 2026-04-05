import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

variable [AddMonoid ι] [GMonoid A]

theorem mk_zero_pow (a : A 0) (n : ℕ) : GradedMonoid.mk _ (a ^ n) = GradedMonoid.mk _ a ^ n := Sigma.ext (nsmul_zero n).symm <| eqRec_heq _ _

