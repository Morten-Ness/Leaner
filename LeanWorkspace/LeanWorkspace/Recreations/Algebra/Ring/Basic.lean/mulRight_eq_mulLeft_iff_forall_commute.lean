import Mathlib

variable {R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

theorem mulRight_eq_mulLeft_iff_forall_commute : AddMonoidHom.mulRight b = AddMonoidHom.mulLeft b ↔ ∀ a, Commute a b := DFunLike.ext_iff

