import Mathlib

variable {M M₀ M₀' G₀ G₀' N A A' B α β : Type*}

variable [AddGroup A] [DistribSMul M A]

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

