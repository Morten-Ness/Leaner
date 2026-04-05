import Mathlib

variable {R S : Type*}

variable [NonUnitalNonAssocCommSemiring R]

theorem mulRight_eq_mulLeft : AddMonoid.End.mulRight = (AddMonoid.End.mulLeft : R →+ AddMonoid.End R) := AddMonoidHom.ext fun _ =>
    Eq.symm <| AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

