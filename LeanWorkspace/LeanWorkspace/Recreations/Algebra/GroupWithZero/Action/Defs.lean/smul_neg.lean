import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [AddGroup A] [DistribSMul M A]

theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) := eq_neg_of_add_eq_zero_left <| by rw [← smul_add, neg_add_cancel, smul_zero]

