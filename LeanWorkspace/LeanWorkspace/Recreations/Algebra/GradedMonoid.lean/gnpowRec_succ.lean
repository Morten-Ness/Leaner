import Mathlib

variable {ι : Type*}

variable (A : ι → Type*)

variable [AddMonoid ι] [GMul A] [GOne A]

theorem gnpowRec_succ (n : ℕ) (a : GradedMonoid A) :
    (GradedMonoid.mk _ <| GradedMonoid.GMonoid.gnpowRec n.succ a.snd) = ⟨_, GradedMonoid.GMonoid.gnpowRec n a.snd⟩ * a := Sigma.ext (succ_nsmul _ _) (heq_of_cast_eq _ rfl).symm

