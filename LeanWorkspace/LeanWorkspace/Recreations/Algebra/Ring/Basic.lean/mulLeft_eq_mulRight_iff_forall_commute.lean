import Mathlib

variable {R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

theorem mulLeft_eq_mulRight_iff_forall_commute : AddMonoidHom.mulLeft a = AddMonoidHom.mulRight a ↔ ∀ b, Commute a b := DFunLike.ext_iff

